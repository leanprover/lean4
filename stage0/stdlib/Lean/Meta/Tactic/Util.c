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
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "terminalTacticsAsSorry"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 90, 215, 151, 242, 202, 226, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 139, .m_capacity = 139, .m_length = 138, .m_data = "when enabled, terminal tactics such as `grind` and `omega` are replaced with `sorry`. Useful for debugging and fixing bootstrapping issues"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 233, 55, 94, 186, 188, 252, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 217, 134, 189, 91, 246, 107, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_debug_terminalTacticsAsSorry;
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 80, 134, 96, 135, 241, 87, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 105, 212, 82, 205, 98, 36, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(141, 108, 151, 68, 40, 185, 49, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 35, 20, 40, 241, 13, 114, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 161, 8, 73, 13, 24, 41, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 240, 21, 38, 82, 97, 50, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(240, 251, 182, 143, 63, 208, 115, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 226, 182, 237, 212, 141, 147, 41)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "skipAssignedInstances"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 172, 231, 36, 182, 217, 37, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "in the `rw` and `simp` tactics, if an instance implicit argument is assigned, do not try to synthesize instance."};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 5, 107, 131, 111, 226, 218, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object* v_mvarId_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_MVarId_getDecl(v_mvarId_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_userName_70_; lean_object* v___x_72_; 
v_userName_70_ = lean_ctor_get(v_a_66_, 0);
lean_inc(v_userName_70_);
lean_dec(v_a_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v_userName_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_userName_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_65_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object* v_mvarId_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_MVarId_getTag(v_mvarId_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object* v_mvarId_90_, lean_object* v_tag_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_mctx_95_; lean_object* v_cache_96_; lean_object* v_zetaDeltaFVarIds_97_; lean_object* v_postponed_98_; lean_object* v_diag_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_110_; 
v___x_94_ = lean_st_ref_take(v_a_92_);
v_mctx_95_ = lean_ctor_get(v___x_94_, 0);
v_cache_96_ = lean_ctor_get(v___x_94_, 1);
v_zetaDeltaFVarIds_97_ = lean_ctor_get(v___x_94_, 2);
v_postponed_98_ = lean_ctor_get(v___x_94_, 3);
v_diag_99_ = lean_ctor_get(v___x_94_, 4);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_110_ == 0)
{
v___x_101_ = v___x_94_;
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_diag_99_);
lean_inc(v_postponed_98_);
lean_inc(v_zetaDeltaFVarIds_97_);
lean_inc(v_cache_96_);
lean_inc(v_mctx_95_);
lean_dec(v___x_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_95_, v_mvarId_90_, v_tag_91_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_cache_96_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_zetaDeltaFVarIds_97_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v_postponed_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v_diag_99_);
v___x_105_ = v_reuseFailAlloc_109_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_st_ref_set(v_a_92_, v___x_105_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object* v_mvarId_111_, lean_object* v_tag_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_MVarId_setTag___redArg(v_mvarId_111_, v_tag_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object* v_mvarId_116_, lean_object* v_tag_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_MVarId_setTag___redArg(v_mvarId_116_, v_tag_117_, v_a_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object* v_mvarId_124_, lean_object* v_tag_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_MVarId_setTag(v_mvarId_124_, v_tag_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object* v_suffix_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = l_Lean_Name_eraseMacroScopes(v_suffix_132_);
v___x_135_ = l_Lean_Name_append(v_x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object* v_suffix_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_appendTag___lam__0(v_suffix_136_, v_x_137_);
lean_dec(v_suffix_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_139_, lean_object* v_suffix_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = l_Lean_Name_hasMacroScopes(v_tag_139_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_appendTag___lam__0(v_suffix_140_, v_tag_139_);
return v___x_142_;
}
else
{
lean_object* v_view_143_; lean_object* v_name_144_; lean_object* v_imported_145_; lean_object* v_ctx_146_; lean_object* v_scopes_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_156_; 
v_view_143_ = l_Lean_extractMacroScopes(v_tag_139_);
v_name_144_ = lean_ctor_get(v_view_143_, 0);
v_imported_145_ = lean_ctor_get(v_view_143_, 1);
v_ctx_146_ = lean_ctor_get(v_view_143_, 2);
v_scopes_147_ = lean_ctor_get(v_view_143_, 3);
v_isSharedCheck_156_ = !lean_is_exclusive(v_view_143_);
if (v_isSharedCheck_156_ == 0)
{
v___x_149_ = v_view_143_;
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_scopes_147_);
lean_inc(v_ctx_146_);
lean_inc(v_imported_145_);
lean_inc(v_name_144_);
lean_dec(v_view_143_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = l_Lean_Meta_appendTag___lam__0(v_suffix_140_, v_name_144_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_imported_145_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_ctx_146_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_scopes_147_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_MacroScopesView_review(v___x_153_);
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object* v_tag_157_, lean_object* v_suffix_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_appendTag(v_tag_157_, v_suffix_158_);
lean_dec(v_suffix_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_160_, lean_object* v_suffix_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc(v_mvarId_160_);
v___x_167_ = l_Lean_MVarId_getTag(v_mvarId_160_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l_Lean_Meta_appendTag(v_a_168_, v_suffix_161_);
v___x_170_ = l_Lean_MVarId_setTag___redArg(v_mvarId_160_, v___x_169_, v_a_163_);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_mvarId_160_);
v_a_171_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_167_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_179_, lean_object* v_suffix_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_appendTagSuffix(v_mvarId_179_, v_suffix_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_suffix_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_187_, lean_object* v_tag_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_type_187_);
v___x_195_ = 2;
v___x_196_ = l_Lean_Meta_mkFreshExprMVar(v___x_194_, v___x_195_, v_tag_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_197_, lean_object* v_tag_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_197_, v_tag_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_214_, lean_object* v_mvarId_215_, lean_object* v_msg_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_217_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_218_ = l_Lean_MessageData_ofName(v_tacticName_214_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_msg_216_);
v___x_223_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_mvarId_215_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v_mctx_236_; lean_object* v_lctx_237_; lean_object* v_options_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
v___x_235_ = lean_st_ref_get(v___y_229_);
v_mctx_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_mctx_236_);
lean_dec(v___x_235_);
v_lctx_237_ = lean_ctor_get(v___y_228_, 2);
v_options_238_ = lean_ctor_get(v___y_230_, 2);
lean_inc_ref(v_options_238_);
lean_inc_ref(v_lctx_237_);
v___x_239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_239_, 0, v_env_234_);
lean_ctor_set(v___x_239_, 1, v_mctx_236_);
lean_ctor_set(v___x_239_, 2, v_lctx_237_);
lean_ctor_set(v___x_239_, 3, v_options_238_);
v___x_240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_msgData_227_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_ref_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_ref_255_ = lean_ctor_get(v___y_252_, 5);
v___x_256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
lean_inc(v_ref_255_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_ref_255_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_276_, lean_object* v_mvarId_277_, lean_object* v_msg_x3f_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
if (lean_obj_tag(v_msg_x3f_278_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_284_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_285_ = l_Lean_MessageData_ofName(v_tacticName_276_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_mvarId_277_);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_290_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_val_292_ = lean_ctor_get(v_msg_x3f_278_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_msg_x3f_278_, 1);
v___x_293_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_276_, v_mvarId_277_, v_val_292_);
v___x_294_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_293_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_295_, lean_object* v_mvarId_296_, lean_object* v_msg_x3f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_295_, v_mvarId_296_, v_msg_x3f_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_304_, lean_object* v_tacticName_305_, lean_object* v_mvarId_306_, lean_object* v_msg_x3f_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_305_, v_mvarId_306_, v_msg_x3f_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_314_, lean_object* v_tacticName_315_, lean_object* v_mvarId_316_, lean_object* v_msg_x3f_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_314_, v_tacticName_315_, v_mvarId_316_, v_msg_x3f_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_324_, lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_332_, lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_332_, v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_346_, lean_object* v_ex_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_nestedMsg_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_msg_359_; lean_object* v_kind_360_; uint8_t v___x_361_; uint8_t v___x_362_; 
v_nestedMsg_353_ = l_Lean_Exception_toMessageData(v_ex_347_);
v___x_354_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_355_ = l_Lean_MessageData_ofName(v_tacticName_346_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_inc_ref(v_nestedMsg_353_);
v_msg_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_359_, 0, v___x_358_);
lean_ctor_set(v_msg_359_, 1, v_nestedMsg_353_);
v_kind_360_ = l_Lean_MessageData_kind(v_nestedMsg_353_);
lean_dec_ref(v_nestedMsg_353_);
v___x_361_ = l_Lean_Name_isAnonymous(v_kind_360_);
v___x_362_ = lean_bool_not(v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_kind_360_);
v___x_363_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_359_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_364_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_365_ = l_Lean_Name_append(v___x_364_, v_kind_360_);
v___x_366_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_msg_359_);
v___x_367_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_366_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_368_, lean_object* v_ex_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_368_, v_ex_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_376_, lean_object* v_tacticName_377_, lean_object* v_ex_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_377_, v_ex_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_385_, lean_object* v_tacticName_386_, lean_object* v_ex_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_385_, v_tacticName_386_, v_ex_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_393_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_394_, lean_object* v_i_395_, lean_object* v_k_396_){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_array_get_size(v_keys_394_);
v___x_398_ = lean_nat_dec_lt(v_i_395_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec(v_i_395_);
return v___x_398_;
}
else
{
lean_object* v_k_x27_399_; uint8_t v___x_400_; 
v_k_x27_399_ = lean_array_fget_borrowed(v_keys_394_, v_i_395_);
v___x_400_ = l_Lean_instBEqMVarId_beq(v_k_396_, v_k_x27_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_nat_add(v_i_395_, v___x_401_);
lean_dec(v_i_395_);
v_i_395_ = v___x_402_;
goto _start;
}
else
{
lean_dec(v_i_395_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_404_, lean_object* v_i_405_, lean_object* v_k_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_404_, v_i_405_, v_k_406_);
lean_dec(v_k_406_);
lean_dec_ref(v_keys_404_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_409_, size_t v_x_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
lean_object* v_es_412_; lean_object* v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v_j_416_; lean_object* v___x_417_; 
v_es_412_ = lean_ctor_get(v_x_409_, 0);
v___x_413_ = lean_box(2);
v___x_414_ = ((size_t)31ULL);
v___x_415_ = lean_usize_land(v_x_410_, v___x_414_);
v_j_416_ = lean_usize_to_nat(v___x_415_);
v___x_417_ = lean_array_get_borrowed(v___x_413_, v_es_412_, v_j_416_);
lean_dec(v_j_416_);
switch(lean_obj_tag(v___x_417_))
{
case 0:
{
lean_object* v_key_418_; uint8_t v___x_419_; 
v_key_418_ = lean_ctor_get(v___x_417_, 0);
v___x_419_ = l_Lean_instBEqMVarId_beq(v_x_411_, v_key_418_);
return v___x_419_;
}
case 1:
{
lean_object* v_node_420_; size_t v___x_421_; size_t v___x_422_; 
v_node_420_ = lean_ctor_get(v___x_417_, 0);
v___x_421_ = ((size_t)5ULL);
v___x_422_ = lean_usize_shift_right(v_x_410_, v___x_421_);
v_x_409_ = v_node_420_;
v_x_410_ = v___x_422_;
goto _start;
}
default: 
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
}
else
{
lean_object* v_ks_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_ks_425_ = lean_ctor_get(v_x_409_, 0);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_425_, v___x_426_, v_x_411_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
size_t v_x_580__boxed_431_; uint8_t v_res_432_; lean_object* v_r_433_; 
v_x_580__boxed_431_ = lean_unbox_usize(v_x_429_);
lean_dec(v_x_429_);
v_res_432_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_428_, v_x_580__boxed_431_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_x_428_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
uint64_t v___x_436_; size_t v___x_437_; uint8_t v___x_438_; 
v___x_436_ = l_Lean_instHashableMVarId_hash(v_x_435_);
v___x_437_ = lean_uint64_to_usize(v___x_436_);
v___x_438_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_434_, v___x_437_, v_x_435_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec_ref(v_x_439_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_mctx_447_; lean_object* v_eAssignment_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_446_ = lean_st_ref_get(v___y_444_);
v_mctx_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_mctx_447_);
lean_dec(v___x_446_);
v_eAssignment_448_ = lean_ctor_get(v_mctx_447_, 8);
lean_inc_ref(v_eAssignment_448_);
lean_dec_ref(v_mctx_447_);
v___x_449_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_448_, v_mvarId_443_);
lean_dec_ref(v_eAssignment_448_);
v___x_450_ = lean_box(v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec(v_mvarId_452_);
return v_res_455_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_463_ = l_Lean_MessageData_ofFormat(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_465_ = l_Lean_MessageData_note(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_467_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_471_, lean_object* v_tacticName_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_490_; 
v___x_478_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_471_, v_a_474_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_490_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_490_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_490_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v___x_483_; 
v___x_483_ = lean_unbox(v_a_479_);
lean_dec(v_a_479_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec(v_tacticName_472_);
lean_dec(v_mvarId_471_);
v___x_484_ = lean_box(0);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_del_object(v___x_481_);
v___x_488_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_489_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_472_, v_mvarId_471_, v___x_488_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_491_, lean_object* v_tacticName_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_491_, v_tacticName_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_499_, v___y_501_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v_mvarId_506_);
return v_res_512_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_517_, v_x_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec_ref(v_x_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_522_, lean_object* v_x_523_, size_t v_x_524_, lean_object* v_x_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_523_, v_x_524_, v_x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
size_t v_x_747__boxed_531_; uint8_t v_res_532_; lean_object* v_r_533_; 
v_x_747__boxed_531_ = lean_unbox_usize(v_x_529_);
lean_dec(v_x_529_);
v_res_532_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_527_, v_x_528_, v_x_747__boxed_531_, v_x_530_);
lean_dec(v_x_530_);
lean_dec_ref(v_x_528_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_534_, lean_object* v_keys_535_, lean_object* v_vals_536_, lean_object* v_heq_537_, lean_object* v_i_538_, lean_object* v_k_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_535_, v_i_538_, v_k_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_541_, lean_object* v_keys_542_, lean_object* v_vals_543_, lean_object* v_heq_544_, lean_object* v_i_545_, lean_object* v_k_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_541_, v_keys_542_, v_vals_543_, v_heq_544_, v_i_545_, v_k_546_);
lean_dec(v_k_546_);
lean_dec_ref(v_vals_543_);
lean_dec_ref(v_keys_542_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_MVarId_getDecl(v_mvarId_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_type_560_; lean_object* v___x_562_; 
v_type_560_ = lean_ctor_get(v_a_556_, 2);
lean_inc_ref(v_type_560_);
lean_dec(v_a_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_type_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_type_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_a_565_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_555_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_MVarId_getType(v_mvarId_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = l_Lean_Expr_hasMVar(v_e_580_);
v___x_584_ = lean_bool_not(v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v_mctx_586_; lean_object* v___x_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_590_; lean_object* v_cache_591_; lean_object* v_zetaDeltaFVarIds_592_; lean_object* v_postponed_593_; lean_object* v_diag_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v___x_585_ = lean_st_ref_get(v___y_581_);
v_mctx_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_mctx_586_);
lean_dec(v___x_585_);
v___x_587_ = l_Lean_instantiateMVarsCore(v_mctx_586_, v_e_580_);
v_fst_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_fst_588_);
v_snd_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_snd_589_);
lean_dec_ref(v___x_587_);
v___x_590_ = lean_st_ref_take(v___y_581_);
v_cache_591_ = lean_ctor_get(v___x_590_, 1);
v_zetaDeltaFVarIds_592_ = lean_ctor_get(v___x_590_, 2);
v_postponed_593_ = lean_ctor_get(v___x_590_, 3);
v_diag_594_ = lean_ctor_get(v___x_590_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_604_);
v___x_596_ = v___x_590_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_diag_594_);
lean_inc(v_postponed_593_);
lean_inc(v_zetaDeltaFVarIds_592_);
lean_inc(v_cache_591_);
lean_dec(v___x_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_snd_589_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_snd_589_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_cache_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_zetaDeltaFVarIds_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_postponed_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_diag_594_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_st_ref_set(v___y_581_, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_fst_588_);
return v___x_601_;
}
}
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_e_580_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_606_, v___y_607_);
lean_dec(v___y_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_610_, v___y_612_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_MVarId_getType(v_mvarId_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
v___x_632_ = lean_whnf(v_a_631_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_633_, v_a_626_);
return v___x_634_;
}
else
{
return v___x_632_;
}
}
else
{
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_MVarId_getType_x27(v_mvarId_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_708_ = 0;
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_710_ = l_Lean_registerTraceClass(v___x_707_, v___x_708_, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_713_, v_x_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
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
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_720_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_720_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_737_, lean_object* v_x_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_737_, v_x_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_745_, lean_object* v_mvarId_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_746_, v_x_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_754_, lean_object* v_mvarId_755_, lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_754_, v_mvarId_755_, v_x_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
lean_object* v_ks_767_; lean_object* v_vs_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_792_; 
v_ks_767_ = lean_ctor_get(v_x_763_, 0);
v_vs_768_ = lean_ctor_get(v_x_763_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_x_763_);
if (v_isSharedCheck_792_ == 0)
{
v___x_770_ = v_x_763_;
v_isShared_771_ = v_isSharedCheck_792_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_vs_768_);
lean_inc(v_ks_767_);
lean_dec(v_x_763_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_792_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_array_get_size(v_ks_767_);
v___x_773_ = lean_nat_dec_lt(v_x_764_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v_x_764_);
v___x_774_ = lean_array_push(v_ks_767_, v_x_765_);
v___x_775_ = lean_array_push(v_vs_768_, v_x_766_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_775_);
lean_ctor_set(v___x_770_, 0, v___x_774_);
v___x_777_ = v___x_770_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v_k_x27_779_; uint8_t v___x_780_; 
v_k_x27_779_ = lean_array_fget_borrowed(v_ks_767_, v_x_764_);
v___x_780_ = l_Lean_instBEqMVarId_beq(v_x_765_, v_k_x27_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_782_; 
if (v_isShared_771_ == 0)
{
v___x_782_ = v___x_770_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_ks_767_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_vs_768_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_x_764_, v___x_783_);
lean_dec(v_x_764_);
v_x_763_ = v___x_782_;
v_x_764_ = v___x_784_;
goto _start;
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_787_ = lean_array_fset(v_ks_767_, v_x_764_, v_x_765_);
v___x_788_ = lean_array_fset(v_vs_768_, v_x_764_, v_x_766_);
lean_dec(v_x_764_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_788_);
lean_ctor_set(v___x_770_, 0, v___x_787_);
v___x_790_ = v___x_770_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_793_, lean_object* v_k_794_, lean_object* v_v_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_793_, v___x_796_, v_k_794_, v_v_795_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_799_, size_t v_x_800_, size_t v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v_es_804_; size_t v___x_805_; size_t v___x_806_; lean_object* v_j_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_es_804_ = lean_ctor_get(v_x_799_, 0);
v___x_805_ = ((size_t)31ULL);
v___x_806_ = lean_usize_land(v_x_800_, v___x_805_);
v_j_807_ = lean_usize_to_nat(v___x_806_);
v___x_808_ = lean_array_get_size(v_es_804_);
v___x_809_ = lean_nat_dec_lt(v_j_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_dec(v_j_807_);
lean_dec(v_x_803_);
lean_dec(v_x_802_);
return v_x_799_;
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_848_; 
lean_inc_ref(v_es_804_);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_x_799_, 0);
lean_dec(v_unused_849_);
v___x_811_ = v_x_799_;
v_isShared_812_ = v_isSharedCheck_848_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_x_799_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_848_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_v_813_; lean_object* v___x_814_; lean_object* v_xs_x27_815_; lean_object* v___y_817_; 
v_v_813_ = lean_array_fget(v_es_804_, v_j_807_);
v___x_814_ = lean_box(0);
v_xs_x27_815_ = lean_array_fset(v_es_804_, v_j_807_, v___x_814_);
switch(lean_obj_tag(v_v_813_))
{
case 0:
{
lean_object* v_key_822_; lean_object* v_val_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v_key_822_ = lean_ctor_get(v_v_813_, 0);
v_val_823_ = lean_ctor_get(v_v_813_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_v_813_);
if (v_isSharedCheck_833_ == 0)
{
v___x_825_ = v_v_813_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_val_823_);
lean_inc(v_key_822_);
lean_dec(v_v_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_instBEqMVarId_beq(v_x_802_, v_key_822_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_825_);
v___x_828_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_822_, v_val_823_, v_x_802_, v_x_803_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___y_817_ = v___x_829_;
goto v___jp_816_;
}
else
{
lean_object* v___x_831_; 
lean_dec(v_val_823_);
lean_dec(v_key_822_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_x_803_);
lean_ctor_set(v___x_825_, 0, v_x_802_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_x_802_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_x_803_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v___y_817_ = v___x_831_;
goto v___jp_816_;
}
}
}
}
case 1:
{
lean_object* v_node_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_846_; 
v_node_834_ = lean_ctor_get(v_v_813_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_v_813_);
if (v_isSharedCheck_846_ == 0)
{
v___x_836_ = v_v_813_;
v_isShared_837_ = v_isSharedCheck_846_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_node_834_);
lean_dec(v_v_813_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_846_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_838_ = ((size_t)5ULL);
v___x_839_ = lean_usize_shift_right(v_x_800_, v___x_838_);
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_x_801_, v___x_840_);
v___x_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_834_, v___x_839_, v___x_841_, v_x_802_, v_x_803_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_842_);
v___x_844_ = v___x_836_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v___y_817_ = v___x_844_;
goto v___jp_816_;
}
}
}
default: 
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_x_802_);
lean_ctor_set(v___x_847_, 1, v_x_803_);
v___y_817_ = v___x_847_;
goto v___jp_816_;
}
}
v___jp_816_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_array_fset(v_xs_x27_815_, v_j_807_, v___y_817_);
lean_dec(v_j_807_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_818_);
v___x_820_ = v___x_811_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_object* v_ks_850_; lean_object* v_vs_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_871_; 
v_ks_850_ = lean_ctor_get(v_x_799_, 0);
v_vs_851_ = lean_ctor_get(v_x_799_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_871_ == 0)
{
v___x_853_ = v_x_799_;
v_isShared_854_ = v_isSharedCheck_871_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_vs_851_);
lean_inc(v_ks_850_);
lean_dec(v_x_799_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_871_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_ks_850_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_vs_851_);
v___x_856_ = v_reuseFailAlloc_870_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v_newNode_857_; uint8_t v___y_859_; size_t v___x_865_; uint8_t v___x_866_; 
v_newNode_857_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_856_, v_x_802_, v_x_803_);
v___x_865_ = ((size_t)7ULL);
v___x_866_ = lean_usize_dec_le(v___x_865_, v_x_801_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_867_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_857_);
v___x_868_ = lean_unsigned_to_nat(4u);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
lean_dec(v___x_867_);
v___y_859_ = v___x_869_;
goto v___jp_858_;
}
else
{
v___y_859_ = v___x_866_;
goto v___jp_858_;
}
v___jp_858_:
{
if (v___y_859_ == 0)
{
lean_object* v_ks_860_; lean_object* v_vs_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_ks_860_ = lean_ctor_get(v_newNode_857_, 0);
lean_inc_ref(v_ks_860_);
v_vs_861_ = lean_ctor_get(v_newNode_857_, 1);
lean_inc_ref(v_vs_861_);
lean_dec_ref(v_newNode_857_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_801_, v_ks_860_, v_vs_861_, v___x_862_, v___x_863_);
lean_dec_ref(v_vs_861_);
lean_dec_ref(v_ks_860_);
return v___x_864_;
}
else
{
return v_newNode_857_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_i_875_, lean_object* v_entries_876_){
_start:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_array_get_size(v_keys_873_);
v___x_878_ = lean_nat_dec_lt(v_i_875_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec(v_i_875_);
return v_entries_876_;
}
else
{
lean_object* v_k_879_; lean_object* v_v_880_; uint64_t v___x_881_; size_t v_h_882_; size_t v___x_883_; lean_object* v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v_h_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_k_879_ = lean_array_fget_borrowed(v_keys_873_, v_i_875_);
v_v_880_ = lean_array_fget_borrowed(v_vals_874_, v_i_875_);
v___x_881_ = l_Lean_instHashableMVarId_hash(v_k_879_);
v_h_882_ = lean_uint64_to_usize(v___x_881_);
v___x_883_ = ((size_t)5ULL);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_sub(v_depth_872_, v___x_885_);
v___x_887_ = lean_usize_mul(v___x_883_, v___x_886_);
v_h_888_ = lean_usize_shift_right(v_h_882_, v___x_887_);
v___x_889_ = lean_nat_add(v_i_875_, v___x_884_);
lean_dec(v_i_875_);
lean_inc(v_v_880_);
lean_inc(v_k_879_);
v___x_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_876_, v_h_888_, v_depth_872_, v_k_879_, v_v_880_);
v_i_875_ = v___x_889_;
v_entries_876_ = v___x_890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_892_, lean_object* v_keys_893_, lean_object* v_vals_894_, lean_object* v_i_895_, lean_object* v_entries_896_){
_start:
{
size_t v_depth_boxed_897_; lean_object* v_res_898_; 
v_depth_boxed_897_ = lean_unbox_usize(v_depth_892_);
lean_dec(v_depth_892_);
v_res_898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_897_, v_keys_893_, v_vals_894_, v_i_895_, v_entries_896_);
lean_dec_ref(v_vals_894_);
lean_dec_ref(v_keys_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
size_t v_x_1007__boxed_904_; size_t v_x_1008__boxed_905_; lean_object* v_res_906_; 
v_x_1007__boxed_904_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_x_1008__boxed_905_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_res_906_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_899_, v_x_1007__boxed_904_, v_x_1008__boxed_905_, v_x_902_, v_x_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
uint64_t v___x_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_910_ = l_Lean_instHashableMVarId_hash(v_x_908_);
v___x_911_ = lean_uint64_to_usize(v___x_910_);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_907_, v___x_911_, v___x_912_, v_x_908_, v_x_909_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_914_, lean_object* v_val_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v_mctx_919_; lean_object* v_cache_920_; lean_object* v_zetaDeltaFVarIds_921_; lean_object* v_postponed_922_; lean_object* v_diag_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_951_; 
v___x_918_ = lean_st_ref_take(v___y_916_);
v_mctx_919_ = lean_ctor_get(v___x_918_, 0);
v_cache_920_ = lean_ctor_get(v___x_918_, 1);
v_zetaDeltaFVarIds_921_ = lean_ctor_get(v___x_918_, 2);
v_postponed_922_ = lean_ctor_get(v___x_918_, 3);
v_diag_923_ = lean_ctor_get(v___x_918_, 4);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_951_ == 0)
{
v___x_925_ = v___x_918_;
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_diag_923_);
lean_inc(v_postponed_922_);
lean_inc(v_zetaDeltaFVarIds_921_);
lean_inc(v_cache_920_);
lean_inc(v_mctx_919_);
lean_dec(v___x_918_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_951_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_depth_927_; lean_object* v_levelAssignDepth_928_; lean_object* v_lmvarCounter_929_; lean_object* v_mvarCounter_930_; lean_object* v_lDecls_931_; lean_object* v_decls_932_; lean_object* v_userNames_933_; lean_object* v_lAssignment_934_; lean_object* v_eAssignment_935_; lean_object* v_dAssignment_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_950_; 
v_depth_927_ = lean_ctor_get(v_mctx_919_, 0);
v_levelAssignDepth_928_ = lean_ctor_get(v_mctx_919_, 1);
v_lmvarCounter_929_ = lean_ctor_get(v_mctx_919_, 2);
v_mvarCounter_930_ = lean_ctor_get(v_mctx_919_, 3);
v_lDecls_931_ = lean_ctor_get(v_mctx_919_, 4);
v_decls_932_ = lean_ctor_get(v_mctx_919_, 5);
v_userNames_933_ = lean_ctor_get(v_mctx_919_, 6);
v_lAssignment_934_ = lean_ctor_get(v_mctx_919_, 7);
v_eAssignment_935_ = lean_ctor_get(v_mctx_919_, 8);
v_dAssignment_936_ = lean_ctor_get(v_mctx_919_, 9);
v_isSharedCheck_950_ = !lean_is_exclusive(v_mctx_919_);
if (v_isSharedCheck_950_ == 0)
{
v___x_938_ = v_mctx_919_;
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_dAssignment_936_);
lean_inc(v_eAssignment_935_);
lean_inc(v_lAssignment_934_);
lean_inc(v_userNames_933_);
lean_inc(v_decls_932_);
lean_inc(v_lDecls_931_);
lean_inc(v_mvarCounter_930_);
lean_inc(v_lmvarCounter_929_);
lean_inc(v_levelAssignDepth_928_);
lean_inc(v_depth_927_);
lean_dec(v_mctx_919_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_935_, v_mvarId_914_, v_val_915_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 8, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_depth_927_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_levelAssignDepth_928_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_lmvarCounter_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_mvarCounter_930_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_lDecls_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 5, v_decls_932_);
lean_ctor_set(v_reuseFailAlloc_949_, 6, v_userNames_933_);
lean_ctor_set(v_reuseFailAlloc_949_, 7, v_lAssignment_934_);
lean_ctor_set(v_reuseFailAlloc_949_, 8, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_949_, 9, v_dAssignment_936_);
v___x_942_ = v_reuseFailAlloc_949_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_942_);
v___x_944_ = v___x_925_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_cache_920_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_zetaDeltaFVarIds_921_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_postponed_922_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_diag_923_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_st_ref_set(v___y_916_, v___x_944_);
v___x_946_ = lean_box(0);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_952_, lean_object* v_val_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_952_, v_val_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_957_, lean_object* v___x_958_, uint8_t v_synthetic_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
lean_inc(v_mvarId_957_);
v___x_965_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_957_, v___x_958_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v___x_966_; 
lean_dec_ref_known(v___x_965_, 1);
lean_inc(v_mvarId_957_);
v___x_966_ = l_Lean_MVarId_getType(v_mvarId_957_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = 1;
v___x_969_ = l_Lean_Meta_mkLabeledSorry(v_a_967_, v_synthetic_959_, v___x_968_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_957_, v_a_970_, v___y_961_);
return v___x_971_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_mvarId_957_);
v_a_972_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_969_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_mvarId_957_);
v_a_980_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_966_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_966_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_dec(v_mvarId_957_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_988_, lean_object* v___x_989_, lean_object* v_synthetic_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v_synthetic_boxed_996_; lean_object* v_res_997_; 
v_synthetic_boxed_996_ = lean_unbox(v_synthetic_990_);
v_res_997_ = l_Lean_MVarId_admit___lam__0(v_mvarId_988_, v___x_989_, v_synthetic_boxed_996_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1001_, uint8_t v_synthetic_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; 
v___x_1008_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1009_ = lean_box(v_synthetic_1002_);
lean_inc(v_mvarId_1001_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1010_, 0, v_mvarId_1001_);
lean_closure_set(v___f_1010_, 1, v___x_1008_);
lean_closure_set(v___f_1010_, 2, v___x_1009_);
v___x_1011_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1001_, v___f_1010_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1012_, lean_object* v_synthetic_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_synthetic_boxed_1019_; lean_object* v_res_1020_; 
v_synthetic_boxed_1019_ = lean_unbox(v_synthetic_1013_);
v_res_1020_ = l_Lean_MVarId_admit(v_mvarId_1012_, v_synthetic_boxed_1019_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1021_, lean_object* v_val_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1021_, v_val_1022_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1029_, lean_object* v_val_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1029_, v_val_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1038_, v_x_1039_, v_x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, size_t v_x_1044_, size_t v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1043_, v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
size_t v_x_1332__boxed_1055_; size_t v_x_1333__boxed_1056_; lean_object* v_res_1057_; 
v_x_1332__boxed_1055_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_x_1333__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_res_1057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1049_, v_x_1050_, v_x_1332__boxed_1055_, v_x_1333__boxed_1056_, v_x_1053_, v_x_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1058_, lean_object* v_n_1059_, lean_object* v_k_1060_, lean_object* v_v_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1059_, v_k_1060_, v_v_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1063_, size_t v_depth_1064_, lean_object* v_keys_1065_, lean_object* v_vals_1066_, lean_object* v_heq_1067_, lean_object* v_i_1068_, lean_object* v_entries_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1064_, v_keys_1065_, v_vals_1066_, v_i_1068_, v_entries_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1071_, lean_object* v_depth_1072_, lean_object* v_keys_1073_, lean_object* v_vals_1074_, lean_object* v_heq_1075_, lean_object* v_i_1076_, lean_object* v_entries_1077_){
_start:
{
size_t v_depth_boxed_1078_; lean_object* v_res_1079_; 
v_depth_boxed_1078_ = lean_unbox_usize(v_depth_1072_);
lean_dec(v_depth_1072_);
v_res_1079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1071_, v_depth_boxed_1078_, v_keys_1073_, v_vals_1074_, v_heq_1075_, v_i_1076_, v_entries_1077_);
lean_dec_ref(v_vals_1074_);
lean_dec_ref(v_keys_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; 
lean_inc(v_mvarId_1086_);
v___x_1092_ = l_Lean_MVarId_getType(v_mvarId_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l_Lean_Expr_headBeta(v_a_1093_);
v___x_1095_ = l_Lean_MVarId_setType___redArg(v_mvarId_1086_, v___x_1094_, v_a_1088_);
return v___x_1095_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_mvarId_1086_);
v_a_1096_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1092_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1092_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_MVarId_headBetaType(v_mvarId_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
uint8_t v___x_1113_; 
v___x_1113_ = 0;
return v___x_1113_;
}
else
{
lean_object* v_key_1114_; lean_object* v_tail_1115_; uint8_t v___x_1116_; 
v_key_1114_ = lean_ctor_get(v_x_1112_, 0);
v_tail_1115_ = lean_ctor_get(v_x_1112_, 2);
v___x_1116_ = l_Lean_instBEqFVarId_beq(v_key_1114_, v_a_1111_);
if (v___x_1116_ == 0)
{
v_x_1112_ = v_tail_1115_;
goto _start;
}
else
{
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1118_, lean_object* v_x_1119_){
_start:
{
uint8_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1118_, v_x_1119_);
lean_dec(v_x_1119_);
lean_dec(v_a_1118_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
return v_x_1123_;
}
else
{
lean_object* v_key_1124_; lean_object* v_value_1125_; lean_object* v_tail_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1135_; 
v_key_1124_ = lean_ctor_get(v_x_1123_, 0);
v_value_1125_ = lean_ctor_get(v_x_1123_, 1);
v_tail_1126_ = lean_ctor_get(v_x_1123_, 2);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1128_ = v_x_1123_;
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_tail_1126_);
lean_inc(v_value_1125_);
lean_inc(v_key_1124_);
lean_dec(v_x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_instBEqFVarId_beq(v_key_1124_, v_a_1122_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1122_, v_tail_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_key_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_value_1125_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
else
{
lean_del_object(v___x_1128_);
lean_dec(v_value_1125_);
lean_dec(v_key_1124_);
return v_tail_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1136_, v_x_1137_);
lean_dec(v_a_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_size_1141_; lean_object* v_buckets_1142_; lean_object* v___x_1143_; uint64_t v___x_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v_fold_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; lean_object* v_bkt_1156_; uint8_t v___x_1157_; 
v_size_1141_ = lean_ctor_get(v_m_1139_, 0);
v_buckets_1142_ = lean_ctor_get(v_m_1139_, 1);
v___x_1143_ = lean_array_get_size(v_buckets_1142_);
v___x_1144_ = l_Lean_instHashableFVarId_hash(v_a_1140_);
v___x_1145_ = 32ULL;
v___x_1146_ = lean_uint64_shift_right(v___x_1144_, v___x_1145_);
v_fold_1147_ = lean_uint64_xor(v___x_1144_, v___x_1146_);
v___x_1148_ = 16ULL;
v___x_1149_ = lean_uint64_shift_right(v_fold_1147_, v___x_1148_);
v___x_1150_ = lean_uint64_xor(v_fold_1147_, v___x_1149_);
v___x_1151_ = lean_uint64_to_usize(v___x_1150_);
v___x_1152_ = lean_usize_of_nat(v___x_1143_);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_sub(v___x_1152_, v___x_1153_);
v___x_1155_ = lean_usize_land(v___x_1151_, v___x_1154_);
v_bkt_1156_ = lean_array_uget_borrowed(v_buckets_1142_, v___x_1155_);
v___x_1157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1140_, v_bkt_1156_);
if (v___x_1157_ == 0)
{
return v_m_1139_;
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1170_; 
lean_inc(v_bkt_1156_);
lean_inc_ref(v_buckets_1142_);
lean_inc(v_size_1141_);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_m_1139_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1171_ = lean_ctor_get(v_m_1139_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_m_1139_, 0);
lean_dec(v_unused_1172_);
v___x_1159_ = v_m_1139_;
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_m_1139_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_buckets_x27_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1161_ = lean_box(0);
v_buckets_x27_1162_ = lean_array_uset(v_buckets_1142_, v___x_1155_, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_sub(v_size_1141_, v___x_1163_);
lean_dec(v_size_1141_);
v___x_1165_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1140_, v_bkt_1156_);
v___x_1166_ = lean_array_uset(v_buckets_x27_1162_, v___x_1155_, v___x_1165_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1166_);
lean_ctor_set(v___x_1159_, 0, v___x_1164_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1173_, v_a_1174_);
lean_dec(v_a_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1183_ = lean_st_ref_take(v___y_1177_);
v___x_1184_ = l_Lean_Expr_fvarId_x21(v_e_1176_);
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1183_, v___x_1184_);
lean_dec(v___x_1184_);
v___x_1186_ = lean_st_ref_set(v___y_1177_, v___x_1185_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v_e_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_st_ref_get(v___y_1198_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_visited_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1217_ = lean_st_ref_get(v_a_1215_);
v_visited_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_visited_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = lean_ptr_addr(v_e_1214_);
v___x_1220_ = ((size_t)8191ULL);
v___x_1221_ = lean_usize_mod(v___x_1219_, v___x_1220_);
v___x_1222_ = lean_array_uget(v_visited_1218_, v___x_1221_);
lean_dec_ref(v_visited_1218_);
v___x_1223_ = lean_ptr_addr(v___x_1222_);
lean_dec(v___x_1222_);
v___x_1224_ = lean_usize_dec_eq(v___x_1223_, v___x_1219_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v_visited_1226_; lean_object* v_checked_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1238_; 
v___x_1225_ = lean_st_ref_take(v_a_1215_);
v_visited_1226_ = lean_ctor_get(v___x_1225_, 0);
v_checked_1227_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1229_ = v___x_1225_;
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_checked_1227_);
lean_inc(v_visited_1226_);
lean_dec(v___x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_array_uset(v_visited_1226_, v___x_1221_, v_e_1214_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_checked_1227_);
v___x_1233_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_st_ref_set(v_a_1215_, v___x_1233_);
v___x_1235_ = lean_box(v___x_1224_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v_e_1214_);
v___x_1239_ = lean_box(v___x_1224_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1241_, v_a_1242_);
lean_dec(v_a_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
return v___x_1247_;
}
else
{
lean_object* v_key_1248_; lean_object* v_tail_1249_; uint8_t v___x_1250_; 
v_key_1248_ = lean_ctor_get(v_x_1246_, 0);
v_tail_1249_ = lean_ctor_get(v_x_1246_, 2);
v___x_1250_ = lean_expr_eqv(v_key_1248_, v_a_1245_);
if (v___x_1250_ == 0)
{
v_x_1246_ = v_tail_1249_;
goto _start;
}
else
{
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1252_, lean_object* v_x_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1252_, v_x_1253_);
lean_dec(v_x_1253_);
lean_dec_ref(v_a_1252_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1257_) == 0)
{
return v_x_1256_;
}
else
{
lean_object* v_key_1258_; lean_object* v_value_1259_; lean_object* v_tail_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1283_; 
v_key_1258_ = lean_ctor_get(v_x_1257_, 0);
v_value_1259_ = lean_ctor_get(v_x_1257_, 1);
v_tail_1260_ = lean_ctor_get(v_x_1257_, 2);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_x_1257_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1262_ = v_x_1257_;
v_isShared_1263_ = v_isSharedCheck_1283_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_tail_1260_);
lean_inc(v_value_1259_);
lean_inc(v_key_1258_);
lean_dec(v_x_1257_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1283_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint64_t v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v_fold_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1264_ = lean_array_get_size(v_x_1256_);
v___x_1265_ = l_Lean_Expr_hash(v_key_1258_);
v___x_1266_ = 32ULL;
v___x_1267_ = lean_uint64_shift_right(v___x_1265_, v___x_1266_);
v_fold_1268_ = lean_uint64_xor(v___x_1265_, v___x_1267_);
v___x_1269_ = 16ULL;
v___x_1270_ = lean_uint64_shift_right(v_fold_1268_, v___x_1269_);
v___x_1271_ = lean_uint64_xor(v_fold_1268_, v___x_1270_);
v___x_1272_ = lean_uint64_to_usize(v___x_1271_);
v___x_1273_ = lean_usize_of_nat(v___x_1264_);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_sub(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_usize_land(v___x_1272_, v___x_1275_);
v___x_1277_ = lean_array_uget_borrowed(v_x_1256_, v___x_1276_);
lean_inc(v___x_1277_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 2, v___x_1277_);
v___x_1279_ = v___x_1262_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_key_1258_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_value_1259_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_array_uset(v_x_1256_, v___x_1276_, v___x_1279_);
v_x_1256_ = v___x_1280_;
v_x_1257_ = v_tail_1260_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1284_, lean_object* v_source_1285_, lean_object* v_target_1286_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_array_get_size(v_source_1285_);
v___x_1288_ = lean_nat_dec_lt(v_i_1284_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_source_1285_);
lean_dec(v_i_1284_);
return v_target_1286_;
}
else
{
lean_object* v_es_1289_; lean_object* v___x_1290_; lean_object* v_source_1291_; lean_object* v_target_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_es_1289_ = lean_array_fget(v_source_1285_, v_i_1284_);
v___x_1290_ = lean_box(0);
v_source_1291_ = lean_array_fset(v_source_1285_, v_i_1284_, v___x_1290_);
v_target_1292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1286_, v_es_1289_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_add(v_i_1284_, v___x_1293_);
lean_dec(v_i_1284_);
v_i_1284_ = v___x_1294_;
v_source_1285_ = v_source_1291_;
v_target_1286_ = v_target_1292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_nbuckets_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1297_ = lean_array_get_size(v_data_1296_);
v___x_1298_ = lean_unsigned_to_nat(2u);
v_nbuckets_1299_ = lean_nat_mul(v___x_1297_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_mk_array(v_nbuckets_1299_, v___x_1301_);
v___x_1303_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1300_, v_data_1296_, v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1304_, lean_object* v_a_1305_, lean_object* v_b_1306_){
_start:
{
lean_object* v_size_1307_; lean_object* v_buckets_1308_; lean_object* v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v_fold_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v_bkt_1322_; uint8_t v___x_1323_; 
v_size_1307_ = lean_ctor_get(v_m_1304_, 0);
v_buckets_1308_ = lean_ctor_get(v_m_1304_, 1);
v___x_1309_ = lean_array_get_size(v_buckets_1308_);
v___x_1310_ = l_Lean_Expr_hash(v_a_1305_);
v___x_1311_ = 32ULL;
v___x_1312_ = lean_uint64_shift_right(v___x_1310_, v___x_1311_);
v_fold_1313_ = lean_uint64_xor(v___x_1310_, v___x_1312_);
v___x_1314_ = 16ULL;
v___x_1315_ = lean_uint64_shift_right(v_fold_1313_, v___x_1314_);
v___x_1316_ = lean_uint64_xor(v_fold_1313_, v___x_1315_);
v___x_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = lean_usize_of_nat(v___x_1309_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_sub(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_usize_land(v___x_1317_, v___x_1320_);
v_bkt_1322_ = lean_array_uget_borrowed(v_buckets_1308_, v___x_1321_);
v___x_1323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1305_, v_bkt_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1344_; 
lean_inc_ref(v_buckets_1308_);
lean_inc(v_size_1307_);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_m_1304_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; lean_object* v_unused_1346_; 
v_unused_1345_ = lean_ctor_get(v_m_1304_, 1);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_m_1304_, 0);
lean_dec(v_unused_1346_);
v___x_1325_ = v_m_1304_;
v_isShared_1326_ = v_isSharedCheck_1344_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_m_1304_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1344_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v_size_x27_1328_; lean_object* v___x_1329_; lean_object* v_buckets_x27_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1327_ = lean_unsigned_to_nat(1u);
v_size_x27_1328_ = lean_nat_add(v_size_1307_, v___x_1327_);
lean_dec(v_size_1307_);
lean_inc(v_bkt_1322_);
v___x_1329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1329_, 0, v_a_1305_);
lean_ctor_set(v___x_1329_, 1, v_b_1306_);
lean_ctor_set(v___x_1329_, 2, v_bkt_1322_);
v_buckets_x27_1330_ = lean_array_uset(v_buckets_1308_, v___x_1321_, v___x_1329_);
v___x_1331_ = lean_unsigned_to_nat(4u);
v___x_1332_ = lean_nat_mul(v_size_x27_1328_, v___x_1331_);
v___x_1333_ = lean_unsigned_to_nat(3u);
v___x_1334_ = lean_nat_div(v___x_1332_, v___x_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_array_get_size(v_buckets_x27_1330_);
v___x_1336_ = lean_nat_dec_le(v___x_1334_, v___x_1335_);
lean_dec(v___x_1334_);
if (v___x_1336_ == 0)
{
lean_object* v_val_1337_; lean_object* v___x_1339_; 
v_val_1337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1330_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_val_1337_);
lean_ctor_set(v___x_1325_, 0, v_size_x27_1328_);
v___x_1339_ = v___x_1325_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_size_x27_1328_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_val_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_object* v___x_1342_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_buckets_x27_1330_);
lean_ctor_set(v___x_1325_, 0, v_size_x27_1328_);
v___x_1342_ = v___x_1325_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_size_x27_1328_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_buckets_x27_1330_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_dec(v_b_1306_);
lean_dec_ref(v_a_1305_);
return v_m_1304_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_buckets_1349_; lean_object* v___x_1350_; uint64_t v___x_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; uint64_t v_fold_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_buckets_1349_ = lean_ctor_get(v_m_1347_, 1);
v___x_1350_ = lean_array_get_size(v_buckets_1349_);
v___x_1351_ = l_Lean_Expr_hash(v_a_1348_);
v___x_1352_ = 32ULL;
v___x_1353_ = lean_uint64_shift_right(v___x_1351_, v___x_1352_);
v_fold_1354_ = lean_uint64_xor(v___x_1351_, v___x_1353_);
v___x_1355_ = 16ULL;
v___x_1356_ = lean_uint64_shift_right(v_fold_1354_, v___x_1355_);
v___x_1357_ = lean_uint64_xor(v_fold_1354_, v___x_1356_);
v___x_1358_ = lean_uint64_to_usize(v___x_1357_);
v___x_1359_ = lean_usize_of_nat(v___x_1350_);
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_sub(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_usize_land(v___x_1358_, v___x_1361_);
v___x_1363_ = lean_array_uget_borrowed(v_buckets_1349_, v___x_1362_);
v___x_1364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1348_, v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1365_, lean_object* v_a_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1365_, v_a_1366_);
lean_dec_ref(v_a_1366_);
lean_dec_ref(v_m_1365_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_checked_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_st_ref_get(v_a_1370_);
v_checked_1373_ = lean_ctor_get(v___x_1372_, 1);
lean_inc_ref(v_checked_1373_);
lean_dec(v___x_1372_);
v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1373_, v_e_1369_);
lean_dec_ref(v_checked_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v_visited_1376_; lean_object* v_checked_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1389_; 
v___x_1375_ = lean_st_ref_take(v_a_1370_);
v_visited_1376_ = lean_ctor_get(v___x_1375_, 0);
v_checked_1377_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1379_ = v___x_1375_;
v_isShared_1380_ = v_isSharedCheck_1389_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_checked_1377_);
lean_inc(v_visited_1376_);
lean_dec(v___x_1375_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1389_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1377_, v_e_1369_, v___x_1381_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_visited_1376_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_st_ref_set(v_a_1370_, v___x_1384_);
v___x_1386_ = lean_box(v___x_1374_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v_e_1369_);
v___x_1390_ = lean_box(v___x_1374_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1392_, v_a_1393_);
lean_dec(v_a_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1396_, lean_object* v_f_1397_, uint8_t v_stopWhenVisited_1398_, lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v_d_1413_; lean_object* v_b_1414_; lean_object* v___y_1415_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___x_1445_; 
lean_inc_ref(v_e_1399_);
v___x_1445_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1478_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1478_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1478_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_unbox(v_a_1446_);
lean_dec(v_a_1446_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
lean_del_object(v___x_1448_);
lean_inc_ref(v_p_1396_);
lean_inc_ref(v_e_1399_);
v___x_1451_ = lean_apply_1(v_p_1396_, v_e_1399_);
v___x_1452_ = lean_unbox(v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1419_ = v_a_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1453_; 
lean_inc_ref(v_e_1399_);
v___x_1453_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; uint8_t v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = lean_unbox(v_a_1454_);
lean_dec(v_a_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_inc_ref(v_f_1397_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v_e_1399_);
v___x_1456_ = lean_apply_7(v_f_1397_, v_e_1399_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, lean_box(0));
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1456_, 0);
lean_dec(v_unused_1465_);
v___x_1458_ = v___x_1456_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_dec(v___x_1456_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
if (v_stopWhenVisited_1398_ == 0)
{
lean_del_object(v___x_1458_);
v___y_1419_ = v_a_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec_ref(v_e_1399_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
v___x_1460_ = lean_box(0);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
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
else
{
lean_dec_ref(v_e_1399_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
return v___x_1456_;
}
}
else
{
v___y_1419_ = v_a_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
goto v___jp_1418_;
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec_ref(v_e_1399_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
v_a_1466_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1453_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1453_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_dec_ref(v_e_1399_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
v___x_1474_ = lean_box(0);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1474_);
v___x_1476_ = v___x_1448_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
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
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_e_1399_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
v_a_1479_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1445_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1445_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1416_; 
lean_inc_ref(v_f_1397_);
lean_inc_ref(v_p_1396_);
v___x_1416_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1396_, v_f_1397_, v_stopWhenVisited_1398_, v_d_1413_, v___y_1415_, v___y_1408_, v___y_1412_, v___y_1411_, v___y_1410_, v___y_1409_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref_known(v___x_1416_, 1);
v_e_1399_ = v_b_1414_;
v_a_1400_ = v___y_1415_;
v___y_1401_ = v___y_1408_;
v___y_1402_ = v___y_1412_;
v___y_1403_ = v___y_1411_;
v___y_1404_ = v___y_1410_;
v___y_1405_ = v___y_1409_;
goto _start;
}
else
{
lean_dec_ref(v_b_1414_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
return v___x_1416_;
}
}
v___jp_1418_:
{
switch(lean_obj_tag(v_e_1399_))
{
case 7:
{
lean_object* v_binderType_1425_; lean_object* v_body_1426_; 
v_binderType_1425_ = lean_ctor_get(v_e_1399_, 1);
lean_inc_ref(v_binderType_1425_);
v_body_1426_ = lean_ctor_get(v_e_1399_, 2);
lean_inc_ref(v_body_1426_);
lean_dec_ref_known(v_e_1399_, 3);
v___y_1408_ = v___y_1420_;
v___y_1409_ = v___y_1424_;
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1422_;
v___y_1412_ = v___y_1421_;
v_d_1413_ = v_binderType_1425_;
v_b_1414_ = v_body_1426_;
v___y_1415_ = v___y_1419_;
goto v___jp_1407_;
}
case 6:
{
lean_object* v_binderType_1427_; lean_object* v_body_1428_; 
v_binderType_1427_ = lean_ctor_get(v_e_1399_, 1);
lean_inc_ref(v_binderType_1427_);
v_body_1428_ = lean_ctor_get(v_e_1399_, 2);
lean_inc_ref(v_body_1428_);
lean_dec_ref_known(v_e_1399_, 3);
v___y_1408_ = v___y_1420_;
v___y_1409_ = v___y_1424_;
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1422_;
v___y_1412_ = v___y_1421_;
v_d_1413_ = v_binderType_1427_;
v_b_1414_ = v_body_1428_;
v___y_1415_ = v___y_1419_;
goto v___jp_1407_;
}
case 8:
{
lean_object* v_type_1429_; lean_object* v_value_1430_; lean_object* v_body_1431_; lean_object* v___x_1432_; 
v_type_1429_ = lean_ctor_get(v_e_1399_, 1);
lean_inc_ref(v_type_1429_);
v_value_1430_ = lean_ctor_get(v_e_1399_, 2);
lean_inc_ref(v_value_1430_);
v_body_1431_ = lean_ctor_get(v_e_1399_, 3);
lean_inc_ref(v_body_1431_);
lean_dec_ref_known(v_e_1399_, 4);
lean_inc_ref(v_f_1397_);
lean_inc_ref(v_p_1396_);
v___x_1432_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1396_, v_f_1397_, v_stopWhenVisited_1398_, v_type_1429_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
lean_dec_ref_known(v___x_1432_, 1);
lean_inc_ref(v_f_1397_);
lean_inc_ref(v_p_1396_);
v___x_1433_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1396_, v_f_1397_, v_stopWhenVisited_1398_, v_value_1430_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref_known(v___x_1433_, 1);
v_e_1399_ = v_body_1431_;
v_a_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
goto _start;
}
else
{
lean_dec_ref(v_body_1431_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
return v___x_1433_;
}
}
else
{
lean_dec_ref(v_body_1431_);
lean_dec_ref(v_value_1430_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
return v___x_1432_;
}
}
case 5:
{
lean_object* v_fn_1435_; lean_object* v_arg_1436_; lean_object* v___x_1437_; 
v_fn_1435_ = lean_ctor_get(v_e_1399_, 0);
lean_inc_ref(v_fn_1435_);
v_arg_1436_ = lean_ctor_get(v_e_1399_, 1);
lean_inc_ref(v_arg_1436_);
lean_dec_ref_known(v_e_1399_, 2);
lean_inc_ref(v_f_1397_);
lean_inc_ref(v_p_1396_);
v___x_1437_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1396_, v_f_1397_, v_stopWhenVisited_1398_, v_fn_1435_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_dec_ref_known(v___x_1437_, 1);
v_e_1399_ = v_arg_1436_;
v_a_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1436_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
return v___x_1437_;
}
}
case 10:
{
lean_object* v_expr_1439_; 
v_expr_1439_ = lean_ctor_get(v_e_1399_, 1);
lean_inc_ref(v_expr_1439_);
lean_dec_ref_known(v_e_1399_, 2);
v_e_1399_ = v_expr_1439_;
v_a_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
goto _start;
}
case 11:
{
lean_object* v_struct_1441_; 
v_struct_1441_ = lean_ctor_get(v_e_1399_, 2);
lean_inc_ref(v_struct_1441_);
lean_dec_ref_known(v_e_1399_, 3);
v_e_1399_ = v_struct_1441_;
v_a_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
goto _start;
}
default: 
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_dec_ref(v_e_1399_);
lean_dec_ref(v_f_1397_);
lean_dec_ref(v_p_1396_);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1487_, lean_object* v_f_1488_, lean_object* v_stopWhenVisited_1489_, lean_object* v_e_1490_, lean_object* v_a_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1498_; lean_object* v_res_1499_; 
v_stopWhenVisited_boxed_1498_ = lean_unbox(v_stopWhenVisited_1489_);
v_res_1499_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1487_, v_f_1488_, v_stopWhenVisited_boxed_1498_, v_e_1490_, v_a_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v_a_1491_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1500_, lean_object* v_f_1501_, lean_object* v_e_1502_, uint8_t v_stopWhenVisited_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = l_Lean_ForEachExprWhere_initCache;
v___x_1511_ = lean_st_mk_ref(v___x_1510_);
v___x_1512_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1500_, v_f_1501_, v_stopWhenVisited_1503_, v_e_1502_, v___x_1511_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_st_ref_get(v___x_1511_);
lean_dec(v___x_1511_);
lean_dec(v___x_1517_);
if (v_isShared_1516_ == 0)
{
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_dec(v___x_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1522_, lean_object* v_f_1523_, lean_object* v_e_1524_, lean_object* v_stopWhenVisited_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1532_; lean_object* v_res_1533_; 
v_stopWhenVisited_boxed_1532_ = lean_unbox(v_stopWhenVisited_1525_);
v_res_1533_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1522_, v_f_1523_, v_e_1524_, v_stopWhenVisited_boxed_1532_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1535_, lean_object* v___f_1536_, uint8_t v___x_1537_, lean_object* v_e_1538_, lean_object* v_candidates_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1538_, v___y_1541_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___y_1549_; uint8_t v___x_1559_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = lean_st_mk_ref(v_candidates_1539_);
v___x_1559_ = l_Lean_Expr_hasFVar(v_a_1546_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_a_1546_);
lean_dec_ref(v___f_1536_);
v___x_1560_ = lean_box(0);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___x_1547_);
v___x_1561_ = lean_apply_7(v___f_1535_, v___x_1560_, v___x_1547_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
v___y_1549_ = v___x_1561_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1563_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1562_, v___f_1536_, v_a_1546_, v___x_1537_, v___x_1547_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___x_1547_);
v___x_1565_ = lean_apply_7(v___f_1535_, v_a_1564_, v___x_1547_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
v___y_1549_ = v___x_1565_;
goto v___jp_1548_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v___x_1547_);
lean_dec_ref(v___f_1535_);
v_a_1566_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1563_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1563_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
v___jp_1548_:
{
if (lean_obj_tag(v___y_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1558_; 
v_a_1550_ = lean_ctor_get(v___y_1549_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___y_1549_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1552_ = v___y_1549_;
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___y_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = lean_st_ref_get(v___x_1547_);
lean_dec(v___x_1547_);
lean_dec(v___x_1554_);
if (v_isShared_1553_ == 0)
{
v___x_1556_ = v___x_1552_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1550_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_dec(v___x_1547_);
return v___y_1549_;
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_candidates_1539_);
lean_dec_ref(v___f_1536_);
lean_dec_ref(v___f_1535_);
v_a_1574_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1545_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1545_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1582_, lean_object* v___f_1583_, lean_object* v___x_1584_, lean_object* v_e_1585_, lean_object* v_candidates_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
uint8_t v___x_17557__boxed_1592_; lean_object* v_res_1593_; 
v___x_17557__boxed_1592_ = lean_unbox(v___x_1584_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1582_, v___f_1583_, v___x_17557__boxed_1592_, v_e_1585_, v_candidates_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_____r_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_st_ref_get(v___y_1595_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_____r_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_e_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1618_ = lean_st_ref_take(v___y_1612_);
v___x_1619_ = l_Lean_Expr_fvarId_x21(v_e_1611_);
v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1618_, v___x_1619_);
lean_dec(v___x_1619_);
v___x_1621_ = lean_st_ref_set(v___y_1612_, v___x_1620_);
v___x_1622_ = lean_box(0);
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_e_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v_e_1624_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 0)
{
return v_x_1632_;
}
else
{
lean_object* v_key_1634_; lean_object* v_value_1635_; lean_object* v_tail_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1659_; 
v_key_1634_ = lean_ctor_get(v_x_1633_, 0);
v_value_1635_ = lean_ctor_get(v_x_1633_, 1);
v_tail_1636_ = lean_ctor_get(v_x_1633_, 2);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1638_ = v_x_1633_;
v_isShared_1639_ = v_isSharedCheck_1659_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_tail_1636_);
lean_inc(v_value_1635_);
lean_inc(v_key_1634_);
lean_dec(v_x_1633_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1659_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; uint64_t v___x_1641_; uint64_t v___x_1642_; uint64_t v___x_1643_; uint64_t v_fold_1644_; uint64_t v___x_1645_; uint64_t v___x_1646_; uint64_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1640_ = lean_array_get_size(v_x_1632_);
v___x_1641_ = l_Lean_instHashableFVarId_hash(v_key_1634_);
v___x_1642_ = 32ULL;
v___x_1643_ = lean_uint64_shift_right(v___x_1641_, v___x_1642_);
v_fold_1644_ = lean_uint64_xor(v___x_1641_, v___x_1643_);
v___x_1645_ = 16ULL;
v___x_1646_ = lean_uint64_shift_right(v_fold_1644_, v___x_1645_);
v___x_1647_ = lean_uint64_xor(v_fold_1644_, v___x_1646_);
v___x_1648_ = lean_uint64_to_usize(v___x_1647_);
v___x_1649_ = lean_usize_of_nat(v___x_1640_);
v___x_1650_ = ((size_t)1ULL);
v___x_1651_ = lean_usize_sub(v___x_1649_, v___x_1650_);
v___x_1652_ = lean_usize_land(v___x_1648_, v___x_1651_);
v___x_1653_ = lean_array_uget_borrowed(v_x_1632_, v___x_1652_);
lean_inc(v___x_1653_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 2, v___x_1653_);
v___x_1655_ = v___x_1638_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_key_1634_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_value_1635_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_array_uset(v_x_1632_, v___x_1652_, v___x_1655_);
v_x_1632_ = v___x_1656_;
v_x_1633_ = v_tail_1636_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1660_, lean_object* v_source_1661_, lean_object* v_target_1662_){
_start:
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = lean_array_get_size(v_source_1661_);
v___x_1664_ = lean_nat_dec_lt(v_i_1660_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_dec_ref(v_source_1661_);
lean_dec(v_i_1660_);
return v_target_1662_;
}
else
{
lean_object* v_es_1665_; lean_object* v___x_1666_; lean_object* v_source_1667_; lean_object* v_target_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_es_1665_ = lean_array_fget(v_source_1661_, v_i_1660_);
v___x_1666_ = lean_box(0);
v_source_1667_ = lean_array_fset(v_source_1661_, v_i_1660_, v___x_1666_);
v_target_1668_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1662_, v_es_1665_);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_i_1660_, v___x_1669_);
lean_dec(v_i_1660_);
v_i_1660_ = v___x_1670_;
v_source_1661_ = v_source_1667_;
v_target_1662_ = v_target_1668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_nbuckets_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1673_ = lean_array_get_size(v_data_1672_);
v___x_1674_ = lean_unsigned_to_nat(2u);
v_nbuckets_1675_ = lean_nat_mul(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_mk_array(v_nbuckets_1675_, v___x_1677_);
v___x_1679_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1676_, v_data_1672_, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v_size_1683_; lean_object* v_buckets_1684_; lean_object* v___x_1685_; uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v_fold_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; lean_object* v_bkt_1698_; uint8_t v___x_1699_; 
v_size_1683_ = lean_ctor_get(v_m_1680_, 0);
v_buckets_1684_ = lean_ctor_get(v_m_1680_, 1);
v___x_1685_ = lean_array_get_size(v_buckets_1684_);
v___x_1686_ = l_Lean_instHashableFVarId_hash(v_a_1681_);
v___x_1687_ = 32ULL;
v___x_1688_ = lean_uint64_shift_right(v___x_1686_, v___x_1687_);
v_fold_1689_ = lean_uint64_xor(v___x_1686_, v___x_1688_);
v___x_1690_ = 16ULL;
v___x_1691_ = lean_uint64_shift_right(v_fold_1689_, v___x_1690_);
v___x_1692_ = lean_uint64_xor(v_fold_1689_, v___x_1691_);
v___x_1693_ = lean_uint64_to_usize(v___x_1692_);
v___x_1694_ = lean_usize_of_nat(v___x_1685_);
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_sub(v___x_1694_, v___x_1695_);
v___x_1697_ = lean_usize_land(v___x_1693_, v___x_1696_);
v_bkt_1698_ = lean_array_uget_borrowed(v_buckets_1684_, v___x_1697_);
v___x_1699_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1681_, v_bkt_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1720_; 
lean_inc_ref(v_buckets_1684_);
lean_inc(v_size_1683_);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_m_1680_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; lean_object* v_unused_1722_; 
v_unused_1721_ = lean_ctor_get(v_m_1680_, 1);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_m_1680_, 0);
lean_dec(v_unused_1722_);
v___x_1701_ = v_m_1680_;
v_isShared_1702_ = v_isSharedCheck_1720_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v_m_1680_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1720_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v_size_x27_1704_; lean_object* v___x_1705_; lean_object* v_buckets_x27_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v_size_x27_1704_ = lean_nat_add(v_size_1683_, v___x_1703_);
lean_dec(v_size_1683_);
lean_inc(v_bkt_1698_);
v___x_1705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1681_);
lean_ctor_set(v___x_1705_, 1, v_b_1682_);
lean_ctor_set(v___x_1705_, 2, v_bkt_1698_);
v_buckets_x27_1706_ = lean_array_uset(v_buckets_1684_, v___x_1697_, v___x_1705_);
v___x_1707_ = lean_unsigned_to_nat(4u);
v___x_1708_ = lean_nat_mul(v_size_x27_1704_, v___x_1707_);
v___x_1709_ = lean_unsigned_to_nat(3u);
v___x_1710_ = lean_nat_div(v___x_1708_, v___x_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_array_get_size(v_buckets_x27_1706_);
v___x_1712_ = lean_nat_dec_le(v___x_1710_, v___x_1711_);
lean_dec(v___x_1710_);
if (v___x_1712_ == 0)
{
lean_object* v_val_1713_; lean_object* v___x_1715_; 
v_val_1713_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1706_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_val_1713_);
lean_ctor_set(v___x_1701_, 0, v_size_x27_1704_);
v___x_1715_ = v___x_1701_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_size_x27_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_val_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
else
{
lean_object* v___x_1718_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_buckets_x27_1706_);
lean_ctor_set(v___x_1701_, 0, v_size_x27_1704_);
v___x_1718_ = v___x_1701_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_size_x27_1704_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_buckets_x27_1706_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_dec(v_b_1682_);
lean_dec(v_a_1681_);
return v_m_1680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1725_, size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_b_1728_);
return v___x_1735_;
}
else
{
lean_object* v_snd_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1799_; 
v_snd_1736_ = lean_ctor_get(v_b_1728_, 1);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_b_1728_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v_b_1728_, 0);
lean_dec(v_unused_1800_);
v___x_1738_ = v_b_1728_;
v_isShared_1739_ = v_isSharedCheck_1799_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_snd_1736_);
lean_dec(v_b_1728_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1799_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v_a_1742_; lean_object* v_a_1749_; 
v___x_1740_ = lean_box(0);
v_a_1749_ = lean_array_uget_borrowed(v_as_1725_, v_i_1727_);
if (lean_obj_tag(v_a_1749_) == 0)
{
v_a_1742_ = v_snd_1736_;
goto v___jp_1741_;
}
else
{
lean_object* v_val_1750_; uint8_t v___x_1751_; 
v_val_1750_ = lean_ctor_get(v_a_1749_, 0);
v___x_1751_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___f_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; lean_object* v_candidates_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___x_1777_; 
v___f_1752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1754_ = l_Lean_LocalDecl_type(v_val_1750_);
lean_inc_ref(v___x_1754_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1752_, v___f_1753_, v___x_1751_, v___x_1754_, v_snd_1736_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l_Lean_LocalDecl_value_x3f(v_val_1750_, v___x_1751_);
if (lean_obj_tag(v___x_1779_) == 0)
{
v_candidates_1756_ = v_a_1778_;
v___y_1757_ = v___y_1729_;
v___y_1758_ = v___y_1730_;
v___y_1759_ = v___y_1731_;
v___y_1760_ = v___y_1732_;
goto v___jp_1755_;
}
else
{
lean_object* v_val_1780_; lean_object* v___x_1781_; 
v_val_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1752_, v___f_1753_, v___x_1751_, v_val_1780_, v_a_1778_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v_candidates_1756_ = v_a_1782_;
v___y_1757_ = v___y_1729_;
v___y_1758_ = v___y_1730_;
v___y_1759_ = v___y_1731_;
v___y_1760_ = v___y_1732_;
goto v___jp_1755_;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v___x_1754_);
lean_del_object(v___x_1738_);
v_a_1783_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1781_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v___x_1754_);
lean_del_object(v___x_1738_);
v_a_1791_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1777_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1777_);
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
v___jp_1755_:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Meta_isProp(v___x_1754_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; uint8_t v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = lean_unbox(v_a_1762_);
lean_dec(v_a_1762_);
if (v___x_1763_ == 0)
{
v_a_1742_ = v_candidates_1756_;
goto v___jp_1741_;
}
else
{
uint8_t v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = l_Lean_LocalDecl_hasValue(v_val_1750_, v___x_1751_);
v___x_1765_ = lean_bool_not(v___x_1764_);
if (v___x_1765_ == 0)
{
v_a_1742_ = v_candidates_1756_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = l_Lean_LocalDecl_fvarId(v_val_1750_);
v___x_1767_ = lean_box(0);
v___x_1768_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1756_, v___x_1766_, v___x_1767_);
v_a_1742_ = v___x_1768_;
goto v___jp_1741_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_candidates_1756_);
lean_del_object(v___x_1738_);
v_a_1769_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1761_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1761_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
v_a_1742_ = v_snd_1736_;
goto v___jp_1741_;
}
}
v___jp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v_a_1742_);
lean_ctor_set(v___x_1738_, 0, v___x_1740_);
v___x_1744_ = v___x_1738_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_a_1742_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
size_t v___x_1745_; size_t v___x_1746_; 
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1727_, v___x_1745_);
v_i_1727_ = v___x_1746_;
v_b_1728_ = v___x_1744_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1801_, lean_object* v_sz_1802_, lean_object* v_i_1803_, lean_object* v_b_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
size_t v_sz_boxed_1810_; size_t v_i_boxed_1811_; lean_object* v_res_1812_; 
v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1802_);
lean_dec(v_sz_1802_);
v_i_boxed_1811_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1801_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec_ref(v_as_1801_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1813_, size_t v_sz_1814_, size_t v_i_1815_, lean_object* v_b_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_usize_dec_lt(v_i_1815_, v_sz_1814_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_b_1816_);
return v___x_1823_;
}
else
{
lean_object* v_snd_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1887_; 
v_snd_1824_ = lean_ctor_get(v_b_1816_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_b_1816_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_b_1816_, 0);
lean_dec(v_unused_1888_);
v___x_1826_ = v_b_1816_;
v_isShared_1827_ = v_isSharedCheck_1887_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_snd_1824_);
lean_dec(v_b_1816_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1887_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v_a_1830_; lean_object* v_a_1837_; 
v___x_1828_ = lean_box(0);
v_a_1837_ = lean_array_uget_borrowed(v_as_1813_, v_i_1815_);
if (lean_obj_tag(v_a_1837_) == 0)
{
v_a_1830_ = v_snd_1824_;
goto v___jp_1829_;
}
else
{
lean_object* v_val_1838_; uint8_t v___x_1839_; 
v_val_1838_ = lean_ctor_get(v_a_1837_, 0);
v___x_1839_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v_candidates_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___x_1865_; 
v___f_1840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1842_ = l_Lean_LocalDecl_type(v_val_1838_);
lean_inc_ref(v___x_1842_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1840_, v___f_1841_, v___x_1839_, v___x_1842_, v_snd_1824_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = l_Lean_LocalDecl_value_x3f(v_val_1838_, v___x_1839_);
if (lean_obj_tag(v___x_1867_) == 0)
{
v_candidates_1844_ = v_a_1866_;
v___y_1845_ = v___y_1817_;
v___y_1846_ = v___y_1818_;
v___y_1847_ = v___y_1819_;
v___y_1848_ = v___y_1820_;
goto v___jp_1843_;
}
else
{
lean_object* v_val_1868_; lean_object* v___x_1869_; 
v_val_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_val_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1840_, v___f_1841_, v___x_1839_, v_val_1868_, v_a_1866_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_candidates_1844_ = v_a_1870_;
v___y_1845_ = v___y_1817_;
v___y_1846_ = v___y_1818_;
v___y_1847_ = v___y_1819_;
v___y_1848_ = v___y_1820_;
goto v___jp_1843_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1842_);
lean_del_object(v___x_1826_);
v_a_1871_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1869_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1869_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v___x_1842_);
lean_del_object(v___x_1826_);
v_a_1879_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1865_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1865_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
v___jp_1843_:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_Meta_isProp(v___x_1842_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; uint8_t v___x_1851_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = lean_unbox(v_a_1850_);
lean_dec(v_a_1850_);
if (v___x_1851_ == 0)
{
v_a_1830_ = v_candidates_1844_;
goto v___jp_1829_;
}
else
{
uint8_t v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = l_Lean_LocalDecl_hasValue(v_val_1838_, v___x_1839_);
v___x_1853_ = lean_bool_not(v___x_1852_);
if (v___x_1853_ == 0)
{
v_a_1830_ = v_candidates_1844_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = l_Lean_LocalDecl_fvarId(v_val_1838_);
v___x_1855_ = lean_box(0);
v___x_1856_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1844_, v___x_1854_, v___x_1855_);
v_a_1830_ = v___x_1856_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_candidates_1844_);
lean_del_object(v___x_1826_);
v_a_1857_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1849_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1849_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
v_a_1830_ = v_snd_1824_;
goto v___jp_1829_;
}
}
v___jp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v_a_1830_);
lean_ctor_set(v___x_1826_, 0, v___x_1828_);
v___x_1832_ = v___x_1826_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_a_1830_);
v___x_1832_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
size_t v___x_1833_; size_t v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1815_, v___x_1833_);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1813_, v_sz_1814_, v___x_1834_, v___x_1832_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1889_, lean_object* v_sz_1890_, lean_object* v_i_1891_, lean_object* v_b_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
size_t v_sz_boxed_1898_; size_t v_i_boxed_1899_; lean_object* v_res_1900_; 
v_sz_boxed_1898_ = lean_unbox_usize(v_sz_1890_);
lean_dec(v_sz_1890_);
v_i_boxed_1899_ = lean_unbox_usize(v_i_1891_);
lean_dec(v_i_1891_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1889_, v_sz_boxed_1898_, v_i_boxed_1899_, v_b_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec_ref(v_as_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1901_, size_t v_sz_1902_, size_t v_i_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_lt(v_i_1903_, v_sz_1902_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_b_1904_);
return v___x_1911_;
}
else
{
lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1975_; 
v_snd_1912_ = lean_ctor_get(v_b_1904_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_b_1904_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_b_1904_, 0);
lean_dec(v_unused_1976_);
v___x_1914_ = v_b_1904_;
v_isShared_1915_ = v_isSharedCheck_1975_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_dec(v_b_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1975_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v_a_1918_; lean_object* v_a_1925_; 
v___x_1916_ = lean_box(0);
v_a_1925_ = lean_array_uget_borrowed(v_as_1901_, v_i_1903_);
if (lean_obj_tag(v_a_1925_) == 0)
{
v_a_1918_ = v_snd_1912_;
goto v___jp_1917_;
}
else
{
lean_object* v_val_1926_; uint8_t v___x_1927_; 
v_val_1926_ = lean_ctor_get(v_a_1925_, 0);
v___x_1927_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; lean_object* v_candidates_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___x_1953_; 
v___f_1928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1930_ = l_Lean_LocalDecl_type(v_val_1926_);
lean_inc_ref(v___x_1930_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1928_, v___f_1929_, v___x_1927_, v___x_1930_, v_snd_1912_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = l_Lean_LocalDecl_value_x3f(v_val_1926_, v___x_1927_);
if (lean_obj_tag(v___x_1955_) == 0)
{
v_candidates_1932_ = v_a_1954_;
v___y_1933_ = v___y_1905_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
goto v___jp_1931_;
}
else
{
lean_object* v_val_1956_; lean_object* v___x_1957_; 
v_val_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_val_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1928_, v___f_1929_, v___x_1927_, v_val_1956_, v_a_1954_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_candidates_1932_ = v_a_1958_;
v___y_1933_ = v___y_1905_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1914_);
v_a_1959_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1957_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1957_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1914_);
v_a_1967_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1953_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1953_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
v___jp_1931_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Meta_isProp(v___x_1930_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; uint8_t v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = lean_unbox(v_a_1938_);
lean_dec(v_a_1938_);
if (v___x_1939_ == 0)
{
v_a_1918_ = v_candidates_1932_;
goto v___jp_1917_;
}
else
{
uint8_t v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = l_Lean_LocalDecl_hasValue(v_val_1926_, v___x_1927_);
v___x_1941_ = lean_bool_not(v___x_1940_);
if (v___x_1941_ == 0)
{
v_a_1918_ = v_candidates_1932_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = l_Lean_LocalDecl_fvarId(v_val_1926_);
v___x_1943_ = lean_box(0);
v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1932_, v___x_1942_, v___x_1943_);
v_a_1918_ = v___x_1944_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_candidates_1932_);
lean_del_object(v___x_1914_);
v_a_1945_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1937_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1937_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
else
{
v_a_1918_ = v_snd_1912_;
goto v___jp_1917_;
}
}
v___jp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v_a_1918_);
lean_ctor_set(v___x_1914_, 0, v___x_1916_);
v___x_1920_ = v___x_1914_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_a_1918_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1903_, v___x_1921_);
v_i_1903_ = v___x_1922_;
v_b_1904_ = v___x_1920_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1977_, lean_object* v_sz_1978_, lean_object* v_i_1979_, lean_object* v_b_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
size_t v_sz_boxed_1986_; size_t v_i_boxed_1987_; lean_object* v_res_1988_; 
v_sz_boxed_1986_ = lean_unbox_usize(v_sz_1978_);
lean_dec(v_sz_1978_);
v_i_boxed_1987_ = lean_unbox_usize(v_i_1979_);
lean_dec(v_i_1979_);
v_res_1988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1977_, v_sz_boxed_1986_, v_i_boxed_1987_, v_b_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec_ref(v_as_1977_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1989_, size_t v_sz_1990_, size_t v_i_1991_, lean_object* v_b_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_lt(v_i_1991_, v_sz_1990_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_b_1992_);
return v___x_1999_;
}
else
{
lean_object* v_snd_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2063_; 
v_snd_2000_ = lean_ctor_get(v_b_1992_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_b_1992_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_b_1992_, 0);
lean_dec(v_unused_2064_);
v___x_2002_ = v_b_1992_;
v_isShared_2003_ = v_isSharedCheck_2063_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_2000_);
lean_dec(v_b_1992_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2063_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v_a_2006_; lean_object* v_a_2013_; 
v___x_2004_ = lean_box(0);
v_a_2013_ = lean_array_uget_borrowed(v_as_1989_, v_i_1991_);
if (lean_obj_tag(v_a_2013_) == 0)
{
v_a_2006_ = v_snd_2000_;
goto v___jp_2005_;
}
else
{
lean_object* v_val_2014_; uint8_t v___x_2015_; 
v_val_2014_ = lean_ctor_get(v_a_2013_, 0);
v___x_2015_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v_candidates_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___x_2041_; 
v___f_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2018_ = l_Lean_LocalDecl_type(v_val_2014_);
lean_inc_ref(v___x_2018_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2016_, v___f_2017_, v___x_2015_, v___x_2018_, v_snd_2000_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_LocalDecl_value_x3f(v_val_2014_, v___x_2015_);
if (lean_obj_tag(v___x_2043_) == 0)
{
v_candidates_2020_ = v_a_2042_;
v___y_2021_ = v___y_1993_;
v___y_2022_ = v___y_1994_;
v___y_2023_ = v___y_1995_;
v___y_2024_ = v___y_1996_;
goto v___jp_2019_;
}
else
{
lean_object* v_val_2044_; lean_object* v___x_2045_; 
v_val_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_val_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2016_, v___f_2017_, v___x_2015_, v_val_2044_, v_a_2042_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v_candidates_2020_ = v_a_2046_;
v___y_2021_ = v___y_1993_;
v___y_2022_ = v___y_1994_;
v___y_2023_ = v___y_1995_;
v___y_2024_ = v___y_1996_;
goto v___jp_2019_;
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2047_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2055_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2041_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2041_);
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
v___jp_2019_:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Meta_isProp(v___x_2018_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; uint8_t v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = lean_unbox(v_a_2026_);
lean_dec(v_a_2026_);
if (v___x_2027_ == 0)
{
v_a_2006_ = v_candidates_2020_;
goto v___jp_2005_;
}
else
{
uint8_t v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_LocalDecl_hasValue(v_val_2014_, v___x_2015_);
v___x_2029_ = lean_bool_not(v___x_2028_);
if (v___x_2029_ == 0)
{
v_a_2006_ = v_candidates_2020_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = l_Lean_LocalDecl_fvarId(v_val_2014_);
v___x_2031_ = lean_box(0);
v___x_2032_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_2020_, v___x_2030_, v___x_2031_);
v_a_2006_ = v___x_2032_;
goto v___jp_2005_;
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref(v_candidates_2020_);
lean_del_object(v___x_2002_);
v_a_2033_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2025_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2025_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
else
{
v_a_2006_ = v_snd_2000_;
goto v___jp_2005_;
}
}
v___jp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v_a_2006_);
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2008_ = v___x_2002_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_a_2006_);
v___x_2008_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_1991_, v___x_2009_);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1989_, v_sz_1990_, v___x_2010_, v___x_2008_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_2011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2065_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec_ref(v_as_2065_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2077_, lean_object* v_n_2078_, lean_object* v_b_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
if (lean_obj_tag(v_n_2078_) == 0)
{
lean_object* v_cs_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; size_t v_sz_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v_cs_2085_ = lean_ctor_get(v_n_2078_, 0);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v_b_2079_);
v_sz_2088_ = lean_array_size(v_cs_2085_);
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2077_, v_cs_2085_, v_sz_2088_, v___x_2089_, v___x_2087_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2105_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_fst_2095_; 
v_fst_2095_ = lean_ctor_get(v_a_2091_, 0);
if (lean_obj_tag(v_fst_2095_) == 0)
{
lean_object* v_snd_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v_snd_2096_ = lean_ctor_get(v_a_2091_, 1);
lean_inc(v_snd_2096_);
lean_dec(v_a_2091_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_snd_2096_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2097_);
v___x_2099_ = v___x_2093_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2103_; 
lean_inc_ref(v_fst_2095_);
lean_dec(v_a_2091_);
v_val_2101_ = lean_ctor_get(v_fst_2095_, 0);
lean_inc(v_val_2101_);
lean_dec_ref_known(v_fst_2095_, 1);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v_val_2101_);
v___x_2103_ = v___x_2093_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_val_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2090_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2090_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_vs_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; size_t v_sz_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v_vs_2114_ = lean_ctor_get(v_n_2078_, 0);
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v_b_2079_);
v_sz_2117_ = lean_array_size(v_vs_2114_);
v___x_2118_ = ((size_t)0ULL);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2114_, v_sz_2117_, v___x_2118_, v___x_2116_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2134_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2134_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2134_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_fst_2124_; 
v_fst_2124_ = lean_ctor_get(v_a_2120_, 0);
if (lean_obj_tag(v_fst_2124_) == 0)
{
lean_object* v_snd_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v_snd_2125_ = lean_ctor_get(v_a_2120_, 1);
lean_inc(v_snd_2125_);
lean_dec(v_a_2120_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_snd_2125_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2126_);
v___x_2128_ = v___x_2122_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
else
{
lean_object* v_val_2130_; lean_object* v___x_2132_; 
lean_inc_ref(v_fst_2124_);
lean_dec(v_a_2120_);
v_val_2130_ = lean_ctor_get(v_fst_2124_, 0);
lean_inc(v_val_2130_);
lean_dec_ref_known(v_fst_2124_, 1);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v_val_2130_);
v___x_2132_ = v___x_2122_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_val_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_a_2135_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2119_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2119_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2143_, lean_object* v_as_2144_, size_t v_sz_2145_, size_t v_i_2146_, lean_object* v_b_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_usize_dec_lt(v_i_2146_, v_sz_2145_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_b_2147_);
return v___x_2154_;
}
else
{
lean_object* v_snd_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2189_; 
v_snd_2155_ = lean_ctor_get(v_b_2147_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_b_2147_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v_b_2147_, 0);
lean_dec(v_unused_2190_);
v___x_2157_ = v_b_2147_;
v_isShared_2158_ = v_isSharedCheck_2189_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_snd_2155_);
lean_dec(v_b_2147_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2189_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v_a_2159_; lean_object* v___x_2160_; 
v_a_2159_ = lean_array_uget_borrowed(v_as_2144_, v_i_2146_);
lean_inc(v_snd_2155_);
v___x_2160_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2143_, v_a_2159_, v_snd_2155_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2180_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2180_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2180_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2161_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2165_);
v___x_2167_ = v___x_2157_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2155_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2167_);
v___x_2169_ = v___x_2163_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
lean_del_object(v___x_2163_);
lean_dec(v_snd_2155_);
v_a_2172_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v_a_2161_, 1);
v___x_2173_ = lean_box(0);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v_a_2172_);
lean_ctor_set(v___x_2157_, 0, v___x_2173_);
v___x_2175_ = v___x_2157_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_a_2172_);
v___x_2175_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
size_t v___x_2176_; size_t v___x_2177_; 
v___x_2176_ = ((size_t)1ULL);
v___x_2177_ = lean_usize_add(v_i_2146_, v___x_2176_);
v_i_2146_ = v___x_2177_;
v_b_2147_ = v___x_2175_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_del_object(v___x_2157_);
lean_dec(v_snd_2155_);
v_a_2181_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2160_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2160_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2191_, lean_object* v_as_2192_, lean_object* v_sz_2193_, lean_object* v_i_2194_, lean_object* v_b_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
size_t v_sz_boxed_2201_; size_t v_i_boxed_2202_; lean_object* v_res_2203_; 
v_sz_boxed_2201_ = lean_unbox_usize(v_sz_2193_);
lean_dec(v_sz_2193_);
v_i_boxed_2202_ = lean_unbox_usize(v_i_2194_);
lean_dec(v_i_2194_);
v_res_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2191_, v_as_2192_, v_sz_boxed_2201_, v_i_boxed_2202_, v_b_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v_as_2192_);
lean_dec_ref(v_init_2191_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2204_, lean_object* v_n_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2204_, v_n_2205_, v_b_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_n_2205_);
lean_dec_ref(v_init_2204_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2213_, lean_object* v_init_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_root_2220_; lean_object* v_tail_2221_; lean_object* v___x_2222_; 
v_root_2220_ = lean_ctor_get(v_t_2213_, 0);
v_tail_2221_ = lean_ctor_get(v_t_2213_, 1);
lean_inc_ref(v_init_2214_);
v___x_2222_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2214_, v_root_2220_, v_init_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec_ref(v_init_2214_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2259_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2259_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2259_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
if (lean_obj_tag(v_a_2223_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; 
v_a_2227_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v_a_2223_, 1);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_a_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
lean_del_object(v___x_2225_);
v_a_2231_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v_a_2223_, 1);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v_a_2231_);
v_sz_2234_ = lean_array_size(v_tail_2221_);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2221_, v_sz_2234_, v___x_2235_, v___x_2233_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2250_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2250_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2250_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_fst_2241_; 
v_fst_2241_ = lean_ctor_get(v_a_2237_, 0);
if (lean_obj_tag(v_fst_2241_) == 0)
{
lean_object* v_snd_2242_; lean_object* v___x_2244_; 
v_snd_2242_ = lean_ctor_get(v_a_2237_, 1);
lean_inc(v_snd_2242_);
lean_dec(v_a_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_snd_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_snd_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
else
{
lean_object* v_val_2246_; lean_object* v___x_2248_; 
lean_inc_ref(v_fst_2241_);
lean_dec(v_a_2237_);
v_val_2246_ = lean_ctor_get(v_fst_2241_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v_fst_2241_, 1);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_val_2246_);
v___x_2248_ = v___x_2239_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_val_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2236_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2236_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2222_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2222_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2268_, lean_object* v_init_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2268_, v_init_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_t_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_buckets_2278_; lean_object* v___x_2279_; uint64_t v___x_2280_; uint64_t v___x_2281_; uint64_t v___x_2282_; uint64_t v_fold_2283_; uint64_t v___x_2284_; uint64_t v___x_2285_; uint64_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
v_buckets_2278_ = lean_ctor_get(v_m_2276_, 1);
v___x_2279_ = lean_array_get_size(v_buckets_2278_);
v___x_2280_ = l_Lean_instHashableFVarId_hash(v_a_2277_);
v___x_2281_ = 32ULL;
v___x_2282_ = lean_uint64_shift_right(v___x_2280_, v___x_2281_);
v_fold_2283_ = lean_uint64_xor(v___x_2280_, v___x_2282_);
v___x_2284_ = 16ULL;
v___x_2285_ = lean_uint64_shift_right(v_fold_2283_, v___x_2284_);
v___x_2286_ = lean_uint64_xor(v_fold_2283_, v___x_2285_);
v___x_2287_ = lean_uint64_to_usize(v___x_2286_);
v___x_2288_ = lean_usize_of_nat(v___x_2279_);
v___x_2289_ = ((size_t)1ULL);
v___x_2290_ = lean_usize_sub(v___x_2288_, v___x_2289_);
v___x_2291_ = lean_usize_land(v___x_2287_, v___x_2290_);
v___x_2292_ = lean_array_uget_borrowed(v_buckets_2278_, v___x_2291_);
v___x_2293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2277_, v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2294_, lean_object* v_a_2295_){
_start:
{
uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_res_2296_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_m_2294_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2298_, lean_object* v_as_2299_, size_t v_sz_2300_, size_t v_i_2301_, lean_object* v_b_2302_){
_start:
{
uint8_t v___x_2304_; 
v___x_2304_ = lean_usize_dec_lt(v_i_2301_, v_sz_2300_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_b_2302_);
return v___x_2305_;
}
else
{
lean_object* v_snd_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2324_; 
v_snd_2306_ = lean_ctor_get(v_b_2302_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_b_2302_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v_b_2302_, 0);
lean_dec(v_unused_2325_);
v___x_2308_ = v_b_2302_;
v_isShared_2309_ = v_isSharedCheck_2324_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snd_2306_);
lean_dec(v_b_2302_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2324_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v_a_2312_; lean_object* v_a_2319_; 
v___x_2310_ = lean_box(0);
v_a_2319_ = lean_array_uget_borrowed(v_as_2299_, v_i_2301_);
if (lean_obj_tag(v_a_2319_) == 0)
{
v_a_2312_ = v_snd_2306_;
goto v___jp_2311_;
}
else
{
lean_object* v_val_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v_val_2320_ = lean_ctor_get(v_a_2319_, 0);
v___x_2321_ = l_Lean_LocalDecl_fvarId(v_val_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2298_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_dec(v___x_2321_);
v_a_2312_ = v_snd_2306_;
goto v___jp_2311_;
}
else
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_array_push(v_snd_2306_, v___x_2321_);
v_a_2312_ = v___x_2323_;
goto v___jp_2311_;
}
}
v___jp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v_a_2312_);
lean_ctor_set(v___x_2308_, 0, v___x_2310_);
v___x_2314_ = v___x_2308_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_a_2312_);
v___x_2314_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
size_t v___x_2315_; size_t v___x_2316_; 
v___x_2315_ = ((size_t)1ULL);
v___x_2316_ = lean_usize_add(v_i_2301_, v___x_2315_);
v_i_2301_ = v___x_2316_;
v_b_2302_ = v___x_2314_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2326_, lean_object* v_as_2327_, lean_object* v_sz_2328_, lean_object* v_i_2329_, lean_object* v_b_2330_, lean_object* v___y_2331_){
_start:
{
size_t v_sz_boxed_2332_; size_t v_i_boxed_2333_; lean_object* v_res_2334_; 
v_sz_boxed_2332_ = lean_unbox_usize(v_sz_2328_);
lean_dec(v_sz_2328_);
v_i_boxed_2333_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2326_, v_as_2327_, v_sz_boxed_2332_, v_i_boxed_2333_, v_b_2330_);
lean_dec_ref(v_as_2327_);
lean_dec_ref(v_a_2326_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2335_, lean_object* v_as_2336_, size_t v_sz_2337_, size_t v_i_2338_, lean_object* v_b_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
uint8_t v___x_2345_; 
v___x_2345_ = lean_usize_dec_lt(v_i_2338_, v_sz_2337_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_b_2339_);
return v___x_2346_;
}
else
{
lean_object* v_snd_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2365_; 
v_snd_2347_ = lean_ctor_get(v_b_2339_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_b_2339_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_b_2339_, 0);
lean_dec(v_unused_2366_);
v___x_2349_ = v_b_2339_;
v_isShared_2350_ = v_isSharedCheck_2365_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_snd_2347_);
lean_dec(v_b_2339_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2365_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v_a_2353_; lean_object* v_a_2360_; 
v___x_2351_ = lean_box(0);
v_a_2360_ = lean_array_uget_borrowed(v_as_2336_, v_i_2338_);
if (lean_obj_tag(v_a_2360_) == 0)
{
v_a_2353_ = v_snd_2347_;
goto v___jp_2352_;
}
else
{
lean_object* v_val_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_val_2361_ = lean_ctor_get(v_a_2360_, 0);
v___x_2362_ = l_Lean_LocalDecl_fvarId(v_val_2361_);
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2335_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_dec(v___x_2362_);
v_a_2353_ = v_snd_2347_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_array_push(v_snd_2347_, v___x_2362_);
v_a_2353_ = v___x_2364_;
goto v___jp_2352_;
}
}
v___jp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v_a_2353_);
lean_ctor_set(v___x_2349_, 0, v___x_2351_);
v___x_2355_ = v___x_2349_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_a_2353_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((size_t)1ULL);
v___x_2357_ = lean_usize_add(v_i_2338_, v___x_2356_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2335_, v_as_2336_, v_sz_2337_, v___x_2357_, v___x_2355_);
return v___x_2358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2367_, lean_object* v_as_2368_, lean_object* v_sz_2369_, lean_object* v_i_2370_, lean_object* v_b_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
size_t v_sz_boxed_2377_; size_t v_i_boxed_2378_; lean_object* v_res_2379_; 
v_sz_boxed_2377_ = lean_unbox_usize(v_sz_2369_);
lean_dec(v_sz_2369_);
v_i_boxed_2378_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_res_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2367_, v_as_2368_, v_sz_boxed_2377_, v_i_boxed_2378_, v_b_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v_as_2368_);
lean_dec_ref(v_a_2367_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2380_, lean_object* v_a_2381_, lean_object* v_n_2382_, lean_object* v_b_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
if (lean_obj_tag(v_n_2382_) == 0)
{
lean_object* v_cs_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; size_t v_sz_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v_cs_2389_ = lean_ctor_get(v_n_2382_, 0);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v_b_2383_);
v_sz_2392_ = lean_array_size(v_cs_2389_);
v___x_2393_ = ((size_t)0ULL);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2380_, v_a_2381_, v_cs_2389_, v_sz_2392_, v___x_2393_, v___x_2391_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2409_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2409_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2409_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_fst_2399_; 
v_fst_2399_ = lean_ctor_get(v_a_2395_, 0);
if (lean_obj_tag(v_fst_2399_) == 0)
{
lean_object* v_snd_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v_snd_2400_ = lean_ctor_get(v_a_2395_, 1);
lean_inc(v_snd_2400_);
lean_dec(v_a_2395_);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_snd_2400_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2401_);
v___x_2403_ = v___x_2397_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
else
{
lean_object* v_val_2405_; lean_object* v___x_2407_; 
lean_inc_ref(v_fst_2399_);
lean_dec(v_a_2395_);
v_val_2405_ = lean_ctor_get(v_fst_2399_, 0);
lean_inc(v_val_2405_);
lean_dec_ref_known(v_fst_2399_, 1);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v_val_2405_);
v___x_2407_ = v___x_2397_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_val_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_a_2410_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2394_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2394_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v_vs_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; size_t v_sz_2421_; size_t v___x_2422_; lean_object* v___x_2423_; 
v_vs_2418_ = lean_ctor_get(v_n_2382_, 0);
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_b_2383_);
v_sz_2421_ = lean_array_size(v_vs_2418_);
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2381_, v_vs_2418_, v_sz_2421_, v___x_2422_, v___x_2420_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2438_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2438_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_fst_2428_; 
v_fst_2428_ = lean_ctor_get(v_a_2424_, 0);
if (lean_obj_tag(v_fst_2428_) == 0)
{
lean_object* v_snd_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v_snd_2429_ = lean_ctor_get(v_a_2424_, 1);
lean_inc(v_snd_2429_);
lean_dec(v_a_2424_);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_snd_2429_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2430_);
v___x_2432_ = v___x_2426_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v_val_2434_; lean_object* v___x_2436_; 
lean_inc_ref(v_fst_2428_);
lean_dec(v_a_2424_);
v_val_2434_ = lean_ctor_get(v_fst_2428_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v_fst_2428_, 1);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v_val_2434_);
v___x_2436_ = v___x_2426_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_val_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_a_2439_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2423_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2423_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2447_, lean_object* v_a_2448_, lean_object* v_as_2449_, size_t v_sz_2450_, size_t v_i_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v___x_2458_; 
v___x_2458_ = lean_usize_dec_lt(v_i_2451_, v_sz_2450_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_b_2452_);
return v___x_2459_;
}
else
{
lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2494_; 
v_snd_2460_ = lean_ctor_get(v_b_2452_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_b_2452_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v_b_2452_, 0);
lean_dec(v_unused_2495_);
v___x_2462_ = v_b_2452_;
v_isShared_2463_ = v_isSharedCheck_2494_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_dec(v_b_2452_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2494_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_array_uget_borrowed(v_as_2449_, v_i_2451_);
lean_inc(v_snd_2460_);
v___x_2465_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2447_, v_a_2448_, v_a_2464_, v_snd_2460_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2485_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2485_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2485_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
if (lean_obj_tag(v_a_2466_) == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2466_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2470_);
v___x_2472_ = v___x_2462_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_snd_2460_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2472_);
v___x_2474_ = v___x_2468_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_del_object(v___x_2468_);
lean_dec(v_snd_2460_);
v_a_2477_ = lean_ctor_get(v_a_2466_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v_a_2466_, 1);
v___x_2478_ = lean_box(0);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v_a_2477_);
lean_ctor_set(v___x_2462_, 0, v___x_2478_);
v___x_2480_ = v___x_2462_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_a_2477_);
v___x_2480_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
size_t v___x_2481_; size_t v___x_2482_; 
v___x_2481_ = ((size_t)1ULL);
v___x_2482_ = lean_usize_add(v_i_2451_, v___x_2481_);
v_i_2451_ = v___x_2482_;
v_b_2452_ = v___x_2480_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_del_object(v___x_2462_);
lean_dec(v_snd_2460_);
v_a_2486_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2465_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2465_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2496_, lean_object* v_a_2497_, lean_object* v_as_2498_, lean_object* v_sz_2499_, lean_object* v_i_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
size_t v_sz_boxed_2507_; size_t v_i_boxed_2508_; lean_object* v_res_2509_; 
v_sz_boxed_2507_ = lean_unbox_usize(v_sz_2499_);
lean_dec(v_sz_2499_);
v_i_boxed_2508_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2496_, v_a_2497_, v_as_2498_, v_sz_boxed_2507_, v_i_boxed_2508_, v_b_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v_as_2498_);
lean_dec_ref(v_a_2497_);
lean_dec_ref(v_init_2496_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2510_, lean_object* v_a_2511_, lean_object* v_n_2512_, lean_object* v_b_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2510_, v_a_2511_, v_n_2512_, v_b_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_n_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_init_2510_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2520_, lean_object* v_as_2521_, size_t v_sz_2522_, size_t v_i_2523_, lean_object* v_b_2524_){
_start:
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_usize_dec_lt(v_i_2523_, v_sz_2522_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_b_2524_);
return v___x_2527_;
}
else
{
lean_object* v_snd_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2546_; 
v_snd_2528_ = lean_ctor_get(v_b_2524_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_b_2524_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v_b_2524_, 0);
lean_dec(v_unused_2547_);
v___x_2530_ = v_b_2524_;
v_isShared_2531_ = v_isSharedCheck_2546_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_snd_2528_);
lean_dec(v_b_2524_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2546_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v_a_2534_; lean_object* v_a_2541_; 
v___x_2532_ = lean_box(0);
v_a_2541_ = lean_array_uget_borrowed(v_as_2521_, v_i_2523_);
if (lean_obj_tag(v_a_2541_) == 0)
{
v_a_2534_ = v_snd_2528_;
goto v___jp_2533_;
}
else
{
lean_object* v_val_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v_val_2542_ = lean_ctor_get(v_a_2541_, 0);
v___x_2543_ = l_Lean_LocalDecl_fvarId(v_val_2542_);
v___x_2544_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2520_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_dec(v___x_2543_);
v_a_2534_ = v_snd_2528_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_array_push(v_snd_2528_, v___x_2543_);
v_a_2534_ = v___x_2545_;
goto v___jp_2533_;
}
}
v___jp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v_a_2534_);
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2536_ = v___x_2530_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_a_2534_);
v___x_2536_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
size_t v___x_2537_; size_t v___x_2538_; 
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2523_, v___x_2537_);
v_i_2523_ = v___x_2538_;
v_b_2524_ = v___x_2536_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2548_, lean_object* v_as_2549_, lean_object* v_sz_2550_, lean_object* v_i_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2550_);
lean_dec(v_sz_2550_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2548_, v_as_2549_, v_sz_boxed_2554_, v_i_boxed_2555_, v_b_2552_);
lean_dec_ref(v_as_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2557_, lean_object* v_as_2558_, size_t v_sz_2559_, size_t v_i_2560_, lean_object* v_b_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
uint8_t v___x_2567_; 
v___x_2567_ = lean_usize_dec_lt(v_i_2560_, v_sz_2559_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_b_2561_);
return v___x_2568_;
}
else
{
lean_object* v_snd_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2587_; 
v_snd_2569_ = lean_ctor_get(v_b_2561_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_b_2561_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_b_2561_, 0);
lean_dec(v_unused_2588_);
v___x_2571_ = v_b_2561_;
v_isShared_2572_ = v_isSharedCheck_2587_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_snd_2569_);
lean_dec(v_b_2561_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2587_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v_a_2575_; lean_object* v_a_2582_; 
v___x_2573_ = lean_box(0);
v_a_2582_ = lean_array_uget_borrowed(v_as_2558_, v_i_2560_);
if (lean_obj_tag(v_a_2582_) == 0)
{
v_a_2575_ = v_snd_2569_;
goto v___jp_2574_;
}
else
{
lean_object* v_val_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v_val_2583_ = lean_ctor_get(v_a_2582_, 0);
v___x_2584_ = l_Lean_LocalDecl_fvarId(v_val_2583_);
v___x_2585_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2557_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_dec(v___x_2584_);
v_a_2575_ = v_snd_2569_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_array_push(v_snd_2569_, v___x_2584_);
v_a_2575_ = v___x_2586_;
goto v___jp_2574_;
}
}
v___jp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_a_2575_);
lean_ctor_set(v___x_2571_, 0, v___x_2573_);
v___x_2577_ = v___x_2571_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_a_2575_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = ((size_t)1ULL);
v___x_2579_ = lean_usize_add(v_i_2560_, v___x_2578_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2557_, v_as_2558_, v_sz_2559_, v___x_2579_, v___x_2577_);
return v___x_2580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2589_, lean_object* v_as_2590_, lean_object* v_sz_2591_, lean_object* v_i_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2591_);
lean_dec(v_sz_2591_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2592_);
lean_dec(v_i_2592_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2589_, v_as_2590_, v_sz_boxed_2599_, v_i_boxed_2600_, v_b_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v_as_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2602_, lean_object* v_t_2603_, lean_object* v_init_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_root_2610_; lean_object* v_tail_2611_; lean_object* v___x_2612_; 
v_root_2610_ = lean_ctor_get(v_t_2603_, 0);
v_tail_2611_ = lean_ctor_get(v_t_2603_, 1);
lean_inc_ref(v_init_2604_);
v___x_2612_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2604_, v_a_2602_, v_root_2610_, v_init_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec_ref(v_init_2604_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2649_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2649_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2649_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_a_2613_, 1);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_a_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; size_t v_sz_2624_; size_t v___x_2625_; lean_object* v___x_2626_; 
lean_del_object(v___x_2615_);
v_a_2621_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v_a_2613_, 1);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_a_2621_);
v_sz_2624_ = lean_array_size(v_tail_2611_);
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2602_, v_tail_2611_, v_sz_2624_, v___x_2625_, v___x_2623_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2640_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2640_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2640_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_fst_2631_; 
v_fst_2631_ = lean_ctor_get(v_a_2627_, 0);
if (lean_obj_tag(v_fst_2631_) == 0)
{
lean_object* v_snd_2632_; lean_object* v___x_2634_; 
v_snd_2632_ = lean_ctor_get(v_a_2627_, 1);
lean_inc(v_snd_2632_);
lean_dec(v_a_2627_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_snd_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_snd_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
else
{
lean_object* v_val_2636_; lean_object* v___x_2638_; 
lean_inc_ref(v_fst_2631_);
lean_dec(v_a_2627_);
v_val_2636_ = lean_ctor_get(v_fst_2631_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v_fst_2631_, 1);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_val_2636_);
v___x_2638_ = v___x_2629_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_val_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2626_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2626_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_a_2650_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2612_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2612_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2658_, lean_object* v_t_2659_, lean_object* v_init_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2658_, v_t_2659_, v_init_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec_ref(v_t_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2669_, lean_object* v_mvarId_2670_, lean_object* v___f_2671_, lean_object* v___f_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_lctx_2678_; lean_object* v_decls_2679_; lean_object* v___x_2680_; 
v_lctx_2678_ = lean_ctor_get(v___y_2673_, 2);
v_decls_2679_ = lean_ctor_get(v_lctx_2678_, 1);
lean_inc_ref(v_decls_2679_);
v___x_2680_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2679_, v_candidates_2669_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l_Lean_MVarId_getType(v_mvarId_2670_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___y_2688_; uint8_t v___x_2712_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2683_, v___y_2674_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref(v___x_2684_);
v___x_2686_ = lean_st_mk_ref(v_a_2681_);
v___x_2712_ = l_Lean_Expr_hasFVar(v_a_2685_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v_a_2685_);
lean_dec_ref(v___f_2672_);
v___x_2713_ = lean_box(0);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc(v___x_2686_);
v___x_2714_ = lean_apply_7(v___f_2671_, v___x_2713_, v___x_2686_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, lean_box(0));
v___y_2688_ = v___x_2714_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2716_ = 0;
v___x_2717_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2715_, v___f_2672_, v_a_2685_, v___x_2716_, v___x_2686_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc(v___x_2686_);
v___x_2719_ = lean_apply_7(v___f_2671_, v_a_2718_, v___x_2686_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, lean_box(0));
v___y_2688_ = v___x_2719_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v___x_2686_);
lean_dec_ref(v_decls_2679_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___f_2671_);
v_a_2720_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2717_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2717_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
v___jp_2687_:
{
if (lean_obj_tag(v___y_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2703_; 
v_a_2689_ = lean_ctor_get(v___y_2688_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___y_2688_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2691_ = v___y_2688_;
v_isShared_2692_ = v_isSharedCheck_2703_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___y_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2703_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v_size_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2693_ = lean_st_ref_get(v___x_2686_);
lean_dec(v___x_2686_);
lean_dec(v___x_2693_);
v_size_2694_ = lean_ctor_get(v_a_2689_, 0);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_nat_dec_eq(v_size_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_del_object(v___x_2691_);
v___x_2697_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2698_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2689_, v_decls_2679_, v___x_2697_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_decls_2679_);
lean_dec(v_a_2689_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_a_2689_);
lean_dec_ref(v_decls_2679_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
v___x_2699_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2699_);
v___x_2701_ = v___x_2691_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v___x_2686_);
lean_dec_ref(v_decls_2679_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
v_a_2704_ = lean_ctor_get(v___y_2688_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___y_2688_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___y_2688_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___y_2688_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_a_2681_);
lean_dec_ref(v_decls_2679_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___f_2672_);
lean_dec_ref(v___f_2671_);
v_a_2728_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2682_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2682_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
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
lean_dec_ref(v_decls_2679_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___f_2672_);
lean_dec_ref(v___f_2671_);
lean_dec(v_mvarId_2670_);
v_a_2736_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2680_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2680_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2744_, lean_object* v_mvarId_2745_, lean_object* v___f_2746_, lean_object* v___f_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2744_, v_mvarId_2745_, v___f_2746_, v___f_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___f_2762_; lean_object* v___f_2763_; lean_object* v_candidates_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; 
v___f_2762_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2763_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2764_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2756_);
v___f_2765_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2765_, 0, v_candidates_2764_);
lean_closure_set(v___f_2765_, 1, v_mvarId_2756_);
lean_closure_set(v___f_2765_, 2, v___f_2763_);
lean_closure_set(v___f_2765_, 3, v___f_2762_);
v___x_2766_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2756_, v___f_2765_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2774_, lean_object* v_m_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2775_, v_a_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2778_, lean_object* v_m_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2778_, v_m_2779_, v_a_2780_);
lean_dec(v_a_2780_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2782_, lean_object* v_m_2783_, lean_object* v_a_2784_, lean_object* v_b_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2783_, v_a_2784_, v_b_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2787_, lean_object* v_m_2788_, lean_object* v_a_2789_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2788_, v_a_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2791_, lean_object* v_m_2792_, lean_object* v_a_2793_){
_start:
{
uint8_t v_res_2794_; lean_object* v_r_2795_; 
v_res_2794_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2791_, v_m_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_m_2792_);
v_r_2795_ = lean_box(v_res_2794_);
return v_r_2795_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2796_, lean_object* v_a_2797_, lean_object* v_x_2798_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2797_, v_x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2800_, lean_object* v_a_2801_, lean_object* v_x_2802_){
_start:
{
uint8_t v_res_2803_; lean_object* v_r_2804_; 
v_res_2803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2800_, v_a_2801_, v_x_2802_);
lean_dec(v_x_2802_);
lean_dec(v_a_2801_);
v_r_2804_ = lean_box(v_res_2803_);
return v_r_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2805_, lean_object* v_a_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2806_, v_x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2809_, lean_object* v_a_2810_, lean_object* v_x_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2809_, v_a_2810_, v_x_2811_);
lean_dec(v_a_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2813_, lean_object* v_a_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2813_, v_a_2814_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2822_, lean_object* v_a_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2822_, v_a_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec(v_a_2823_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2831_, lean_object* v_data_2832_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2834_, lean_object* v_a_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2834_, v_a_2835_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2843_, lean_object* v_a_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2843_, v_a_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v_a_2844_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2852_, lean_object* v_i_2853_, lean_object* v_source_2854_, lean_object* v_target_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2853_, v_source_2854_, v_target_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2857_, lean_object* v_as_2858_, size_t v_sz_2859_, size_t v_i_2860_, lean_object* v_b_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2857_, v_as_2858_, v_sz_2859_, v_i_2860_, v_b_2861_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2868_, lean_object* v_as_2869_, lean_object* v_sz_2870_, lean_object* v_i_2871_, lean_object* v_b_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
size_t v_sz_boxed_2878_; size_t v_i_boxed_2879_; lean_object* v_res_2880_; 
v_sz_boxed_2878_ = lean_unbox_usize(v_sz_2870_);
lean_dec(v_sz_2870_);
v_i_boxed_2879_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2868_, v_as_2869_, v_sz_boxed_2878_, v_i_boxed_2879_, v_b_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_as_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2880_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2881_, lean_object* v_m_2882_, lean_object* v_a_2883_){
_start:
{
uint8_t v___x_2884_; 
v___x_2884_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2882_, v_a_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2885_, lean_object* v_m_2886_, lean_object* v_a_2887_){
_start:
{
uint8_t v_res_2888_; lean_object* v_r_2889_; 
v_res_2888_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2885_, v_m_2886_, v_a_2887_);
lean_dec_ref(v_a_2887_);
lean_dec_ref(v_m_2886_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2890_, lean_object* v_m_2891_, lean_object* v_a_2892_, lean_object* v_b_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2891_, v_a_2892_, v_b_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2895_, lean_object* v_x_2896_, lean_object* v_x_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2896_, v_x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2899_, lean_object* v_as_2900_, size_t v_sz_2901_, size_t v_i_2902_, lean_object* v_b_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2899_, v_as_2900_, v_sz_2901_, v_i_2902_, v_b_2903_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2910_, lean_object* v_as_2911_, lean_object* v_sz_2912_, lean_object* v_i_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
size_t v_sz_boxed_2920_; size_t v_i_boxed_2921_; lean_object* v_res_2922_; 
v_sz_boxed_2920_ = lean_unbox_usize(v_sz_2912_);
lean_dec(v_sz_2912_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2913_);
lean_dec(v_i_2913_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2910_, v_as_2911_, v_sz_boxed_2920_, v_i_boxed_2921_, v_b_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec_ref(v_as_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2922_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2923_, lean_object* v_a_2924_, lean_object* v_x_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2924_, v_x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2927_, lean_object* v_a_2928_, lean_object* v_x_2929_){
_start:
{
uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_res_2930_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2927_, v_a_2928_, v_x_2929_);
lean_dec(v_x_2929_);
lean_dec_ref(v_a_2928_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2932_, lean_object* v_data_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2935_, lean_object* v_i_2936_, lean_object* v_source_2937_, lean_object* v_target_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2936_, v_source_2937_, v_target_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2940_, lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2941_, v_x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = l_Lean_maxRecDepthErrorMessage;
v___x_2950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2952_ = l_Lean_MessageData_ofFormat(v___x_2951_);
return v___x_2952_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2954_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2955_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v___x_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2956_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_ref_2956_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2964_, lean_object* v_ref_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2965_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_2973_, lean_object* v_ref_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_2973_, v_ref_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_2982_, lean_object* v_mvarId_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_fileName_2990_; lean_object* v_fileMap_2991_; lean_object* v_options_2992_; lean_object* v_currRecDepth_2993_; lean_object* v_maxRecDepth_2994_; lean_object* v_ref_2995_; lean_object* v_currNamespace_2996_; lean_object* v_openDecls_2997_; lean_object* v_initHeartbeats_2998_; lean_object* v_maxHeartbeats_2999_; lean_object* v_quotContext_3000_; lean_object* v_currMacroScope_3001_; uint8_t v_diag_3002_; lean_object* v_cancelTk_x3f_3003_; uint8_t v_suppressElabErrors_3004_; lean_object* v_inheritedTraceOptions_3005_; uint8_t v___y_3007_; lean_object* v___x_3035_; uint8_t v___x_3036_; uint8_t v___x_3037_; 
v_fileName_2990_ = lean_ctor_get(v_a_2987_, 0);
v_fileMap_2991_ = lean_ctor_get(v_a_2987_, 1);
v_options_2992_ = lean_ctor_get(v_a_2987_, 2);
v_currRecDepth_2993_ = lean_ctor_get(v_a_2987_, 3);
v_maxRecDepth_2994_ = lean_ctor_get(v_a_2987_, 4);
v_ref_2995_ = lean_ctor_get(v_a_2987_, 5);
v_currNamespace_2996_ = lean_ctor_get(v_a_2987_, 6);
v_openDecls_2997_ = lean_ctor_get(v_a_2987_, 7);
v_initHeartbeats_2998_ = lean_ctor_get(v_a_2987_, 8);
v_maxHeartbeats_2999_ = lean_ctor_get(v_a_2987_, 9);
v_quotContext_3000_ = lean_ctor_get(v_a_2987_, 10);
v_currMacroScope_3001_ = lean_ctor_get(v_a_2987_, 11);
v_diag_3002_ = lean_ctor_get_uint8(v_a_2987_, sizeof(void*)*14);
v_cancelTk_x3f_3003_ = lean_ctor_get(v_a_2987_, 12);
v_suppressElabErrors_3004_ = lean_ctor_get_uint8(v_a_2987_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3005_ = lean_ctor_get(v_a_2987_, 13);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_nat_dec_eq(v_maxRecDepth_2994_, v___x_3035_);
v___x_3037_ = lean_bool_not(v___x_3036_);
if (v___x_3037_ == 0)
{
v___y_3007_ = v___x_3037_;
goto v___jp_3006_;
}
else
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_nat_dec_eq(v_currRecDepth_2993_, v_maxRecDepth_2994_);
v___y_3007_ = v___x_3038_;
goto v___jp_3006_;
}
v___jp_3006_:
{
if (v___y_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3008_ = lean_unsigned_to_nat(1u);
v___x_3009_ = lean_nat_add(v_currRecDepth_2993_, v___x_3008_);
lean_inc_ref(v_inheritedTraceOptions_3005_);
lean_inc(v_cancelTk_x3f_3003_);
lean_inc(v_currMacroScope_3001_);
lean_inc(v_quotContext_3000_);
lean_inc(v_maxHeartbeats_2999_);
lean_inc(v_initHeartbeats_2998_);
lean_inc(v_openDecls_2997_);
lean_inc(v_currNamespace_2996_);
lean_inc(v_ref_2995_);
lean_inc(v_maxRecDepth_2994_);
lean_inc_ref(v_options_2992_);
lean_inc_ref(v_fileMap_2991_);
lean_inc_ref(v_fileName_2990_);
v___x_3010_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3010_, 0, v_fileName_2990_);
lean_ctor_set(v___x_3010_, 1, v_fileMap_2991_);
lean_ctor_set(v___x_3010_, 2, v_options_2992_);
lean_ctor_set(v___x_3010_, 3, v___x_3009_);
lean_ctor_set(v___x_3010_, 4, v_maxRecDepth_2994_);
lean_ctor_set(v___x_3010_, 5, v_ref_2995_);
lean_ctor_set(v___x_3010_, 6, v_currNamespace_2996_);
lean_ctor_set(v___x_3010_, 7, v_openDecls_2997_);
lean_ctor_set(v___x_3010_, 8, v_initHeartbeats_2998_);
lean_ctor_set(v___x_3010_, 9, v_maxHeartbeats_2999_);
lean_ctor_set(v___x_3010_, 10, v_quotContext_3000_);
lean_ctor_set(v___x_3010_, 11, v_currMacroScope_3001_);
lean_ctor_set(v___x_3010_, 12, v_cancelTk_x3f_3003_);
lean_ctor_set(v___x_3010_, 13, v_inheritedTraceOptions_3005_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*14, v_diag_3002_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*14 + 1, v_suppressElabErrors_3004_);
lean_inc_ref(v_x_2982_);
lean_inc(v_a_2988_);
lean_inc_ref(v___x_3010_);
lean_inc(v_a_2986_);
lean_inc_ref(v_a_2985_);
lean_inc(v_mvarId_2983_);
v___x_3011_ = lean_apply_6(v_x_2982_, v_mvarId_2983_, v_a_2985_, v_a_2986_, v___x_3010_, v_a_2988_, lean_box(0));
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3025_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3025_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3025_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
if (lean_obj_tag(v_a_3012_) == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
lean_dec_ref_known(v___x_3010_, 14);
lean_dec_ref(v_x_2982_);
v___x_3016_ = lean_st_ref_take(v_a_2984_);
v___x_3017_ = lean_array_push(v___x_3016_, v_mvarId_2983_);
v___x_3018_ = lean_st_ref_set(v_a_2984_, v___x_3017_);
v___x_3019_ = lean_box(0);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3019_);
v___x_3021_ = v___x_3014_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
else
{
lean_object* v_val_3023_; lean_object* v___x_3024_; 
lean_del_object(v___x_3014_);
lean_dec(v_mvarId_2983_);
v_val_3023_ = lean_ctor_get(v_a_3012_, 0);
lean_inc(v_val_3023_);
lean_dec_ref_known(v_a_3012_, 1);
v___x_3024_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_2982_, v_val_3023_, v_a_2984_, v_a_2985_, v_a_2986_, v___x_3010_, v_a_2988_);
lean_dec_ref_known(v___x_3010_, 14);
return v___x_3024_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref_known(v___x_3010_, 14);
lean_dec(v_mvarId_2983_);
lean_dec_ref(v_x_2982_);
v_a_3026_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3011_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3011_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v___x_3034_; 
lean_dec(v_mvarId_2983_);
lean_dec_ref(v_x_2982_);
lean_inc(v_ref_2995_);
v___x_3034_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2995_);
return v___x_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3039_, lean_object* v_as_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
if (lean_obj_tag(v_as_3040_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v_x_3039_);
v___x_3047_ = lean_box(0);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
else
{
lean_object* v_head_3049_; lean_object* v_tail_3050_; lean_object* v___x_3051_; 
v_head_3049_ = lean_ctor_get(v_as_3040_, 0);
lean_inc(v_head_3049_);
v_tail_3050_ = lean_ctor_get(v_as_3040_, 1);
lean_inc(v_tail_3050_);
lean_dec_ref_known(v_as_3040_, 2);
lean_inc_ref(v_x_3039_);
v___x_3051_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3039_, v_head_3049_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref_known(v___x_3051_, 1);
v_as_3040_ = v_tail_3050_;
goto _start;
}
else
{
lean_dec(v_tail_3050_);
lean_dec_ref(v_x_3039_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3053_, lean_object* v_as_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3053_, v_as_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3062_, lean_object* v_mvarId_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3062_, v_mvarId_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3071_, lean_object* v_x_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3079_ = lean_st_mk_ref(v___x_3078_);
v___x_3080_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3072_, v_mvarId_3071_, v___x_3079_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3089_; 
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3090_);
v___x_3082_ = v___x_3080_;
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v___x_3080_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3084_ = lean_st_ref_get(v___x_3079_);
lean_dec(v___x_3079_);
v___x_3085_ = lean_array_to_list(v___x_3084_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3085_);
v___x_3087_ = v___x_3082_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v___x_3079_);
v_a_3091_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3080_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3080_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3099_, lean_object* v_x_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Meta_saturate(v_mvarId_3099_, v_x_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3107_, lean_object* v_msg_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
if (lean_obj_tag(v_mvarIds_3107_) == 1)
{
lean_object* v_tail_3114_; 
v_tail_3114_ = lean_ctor_get(v_mvarIds_3107_, 1);
if (lean_obj_tag(v_tail_3114_) == 0)
{
lean_object* v_head_3115_; lean_object* v___x_3116_; 
lean_dec_ref(v_msg_3108_);
v_head_3115_ = lean_ctor_get(v_mvarIds_3107_, 0);
lean_inc(v_head_3115_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_head_3115_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
return v___x_3117_;
}
}
else
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3119_, lean_object* v_msg_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_exactlyOne(v_mvarIds_3119_, v_msg_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_mvarIds_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3127_, lean_object* v_msg_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
if (lean_obj_tag(v_mvarIds_3127_) == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_msg_3128_);
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v_tail_3136_; 
v_tail_3136_ = lean_ctor_get(v_mvarIds_3127_, 1);
if (lean_obj_tag(v_tail_3136_) == 0)
{
lean_object* v_head_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec_ref(v_msg_3128_);
v_head_3137_ = lean_ctor_get(v_mvarIds_3127_, 0);
lean_inc(v_head_3137_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_head_3137_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3141_, lean_object* v_msg_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3141_, v_msg_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_mvarIds_3141_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3149_, size_t v_sz_3150_, size_t v_i_3151_, lean_object* v_b_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_lt(v_i_3151_, v_sz_3150_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_b_3152_);
return v___x_3159_;
}
else
{
lean_object* v_snd_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3190_; 
v_snd_3160_ = lean_ctor_get(v_b_3152_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_b_3152_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_b_3152_, 0);
lean_dec(v_unused_3191_);
v___x_3162_ = v_b_3152_;
v_isShared_3163_ = v_isSharedCheck_3190_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3160_);
lean_dec(v_b_3152_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3190_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v_a_3166_; lean_object* v_a_3173_; 
v___x_3164_ = lean_box(0);
v_a_3173_ = lean_array_uget_borrowed(v_as_3149_, v_i_3151_);
if (lean_obj_tag(v_a_3173_) == 0)
{
v_a_3166_ = v_snd_3160_;
goto v___jp_3165_;
}
else
{
lean_object* v_val_3174_; uint8_t v___x_3175_; 
v_val_3174_ = lean_ctor_get(v_a_3173_, 0);
v___x_3175_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = l_Lean_LocalDecl_type(v_val_3174_);
v___x_3177_ = l_Lean_Meta_isProp(v___x_3176_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; uint8_t v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = lean_unbox(v_a_3178_);
lean_dec(v_a_3178_);
if (v___x_3179_ == 0)
{
v_a_3166_ = v_snd_3160_;
goto v___jp_3165_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = l_Lean_LocalDecl_fvarId(v_val_3174_);
v___x_3181_ = lean_array_push(v_snd_3160_, v___x_3180_);
v_a_3166_ = v___x_3181_;
goto v___jp_3165_;
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_del_object(v___x_3162_);
lean_dec(v_snd_3160_);
v_a_3182_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3177_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3177_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
v_a_3166_ = v_snd_3160_;
goto v___jp_3165_;
}
}
v___jp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v_a_3166_);
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3168_ = v___x_3162_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3166_);
v___x_3168_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
size_t v___x_3169_; size_t v___x_3170_; 
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_add(v_i_3151_, v___x_3169_);
v_i_3151_ = v___x_3170_;
v_b_3152_ = v___x_3168_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3192_, lean_object* v_sz_3193_, lean_object* v_i_3194_, lean_object* v_b_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
size_t v_sz_boxed_3201_; size_t v_i_boxed_3202_; lean_object* v_res_3203_; 
v_sz_boxed_3201_ = lean_unbox_usize(v_sz_3193_);
lean_dec(v_sz_3193_);
v_i_boxed_3202_ = lean_unbox_usize(v_i_3194_);
lean_dec(v_i_3194_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3192_, v_sz_boxed_3201_, v_i_boxed_3202_, v_b_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec_ref(v_as_3192_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3204_, size_t v_sz_3205_, size_t v_i_3206_, lean_object* v_b_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_usize_dec_lt(v_i_3206_, v_sz_3205_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_b_3207_);
return v___x_3214_;
}
else
{
lean_object* v_snd_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3245_; 
v_snd_3215_ = lean_ctor_get(v_b_3207_, 1);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_b_3207_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_b_3207_, 0);
lean_dec(v_unused_3246_);
v___x_3217_ = v_b_3207_;
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_snd_3215_);
lean_dec(v_b_3207_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v_a_3221_; lean_object* v_a_3228_; 
v___x_3219_ = lean_box(0);
v_a_3228_ = lean_array_uget_borrowed(v_as_3204_, v_i_3206_);
if (lean_obj_tag(v_a_3228_) == 0)
{
v_a_3221_ = v_snd_3215_;
goto v___jp_3220_;
}
else
{
lean_object* v_val_3229_; uint8_t v___x_3230_; 
v_val_3229_ = lean_ctor_get(v_a_3228_, 0);
v___x_3230_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = l_Lean_LocalDecl_type(v_val_3229_);
v___x_3232_ = l_Lean_Meta_isProp(v___x_3231_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; uint8_t v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = lean_unbox(v_a_3233_);
lean_dec(v_a_3233_);
if (v___x_3234_ == 0)
{
v_a_3221_ = v_snd_3215_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = l_Lean_LocalDecl_fvarId(v_val_3229_);
v___x_3236_ = lean_array_push(v_snd_3215_, v___x_3235_);
v_a_3221_ = v___x_3236_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_del_object(v___x_3217_);
lean_dec(v_snd_3215_);
v_a_3237_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3232_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3232_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
v_a_3221_ = v_snd_3215_;
goto v___jp_3220_;
}
}
v___jp_3220_:
{
lean_object* v___x_3223_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 1, v_a_3221_);
lean_ctor_set(v___x_3217_, 0, v___x_3219_);
v___x_3223_ = v___x_3217_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_a_3221_);
v___x_3223_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = ((size_t)1ULL);
v___x_3225_ = lean_usize_add(v_i_3206_, v___x_3224_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3204_, v_sz_3205_, v___x_3225_, v___x_3223_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3247_, lean_object* v_sz_3248_, lean_object* v_i_3249_, lean_object* v_b_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
size_t v_sz_boxed_3256_; size_t v_i_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3256_ = lean_unbox_usize(v_sz_3248_);
lean_dec(v_sz_3248_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3247_, v_sz_boxed_3256_, v_i_boxed_3257_, v_b_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_as_3247_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3259_, lean_object* v_n_3260_, lean_object* v_b_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
if (lean_obj_tag(v_n_3260_) == 0)
{
lean_object* v_cs_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; size_t v_sz_3270_; size_t v___x_3271_; lean_object* v___x_3272_; 
v_cs_3267_ = lean_ctor_get(v_n_3260_, 0);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v_b_3261_);
v_sz_3270_ = lean_array_size(v_cs_3267_);
v___x_3271_ = ((size_t)0ULL);
v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3259_, v_cs_3267_, v_sz_3270_, v___x_3271_, v___x_3269_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3287_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_fst_3277_; 
v_fst_3277_ = lean_ctor_get(v_a_3273_, 0);
if (lean_obj_tag(v_fst_3277_) == 0)
{
lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v_snd_3278_ = lean_ctor_get(v_a_3273_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_a_3273_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_snd_3278_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3279_);
v___x_3281_ = v___x_3275_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
else
{
lean_object* v_val_3283_; lean_object* v___x_3285_; 
lean_inc_ref(v_fst_3277_);
lean_dec(v_a_3273_);
v_val_3283_ = lean_ctor_get(v_fst_3277_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v_fst_3277_, 1);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v_val_3283_);
v___x_3285_ = v___x_3275_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_val_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3272_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3272_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_vs_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; size_t v_sz_3299_; size_t v___x_3300_; lean_object* v___x_3301_; 
v_vs_3296_ = lean_ctor_get(v_n_3260_, 0);
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v_b_3261_);
v_sz_3299_ = lean_array_size(v_vs_3296_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3296_, v_sz_3299_, v___x_3300_, v___x_3298_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3316_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_fst_3306_; 
v_fst_3306_ = lean_ctor_get(v_a_3302_, 0);
if (lean_obj_tag(v_fst_3306_) == 0)
{
lean_object* v_snd_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v_snd_3307_ = lean_ctor_get(v_a_3302_, 1);
lean_inc(v_snd_3307_);
lean_dec(v_a_3302_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_snd_3307_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3308_);
v___x_3310_ = v___x_3304_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
else
{
lean_object* v_val_3312_; lean_object* v___x_3314_; 
lean_inc_ref(v_fst_3306_);
lean_dec(v_a_3302_);
v_val_3312_ = lean_ctor_get(v_fst_3306_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v_fst_3306_, 1);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v_val_3312_);
v___x_3314_ = v___x_3304_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_val_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3301_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3301_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3325_, lean_object* v_as_3326_, size_t v_sz_3327_, size_t v_i_3328_, lean_object* v_b_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_lt(v_i_3328_, v_sz_3327_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_b_3329_);
return v___x_3336_;
}
else
{
lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3371_; 
v_snd_3337_ = lean_ctor_get(v_b_3329_, 1);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_b_3329_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v_b_3329_, 0);
lean_dec(v_unused_3372_);
v___x_3339_ = v_b_3329_;
v_isShared_3340_ = v_isSharedCheck_3371_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_dec(v_b_3329_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3371_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_a_3341_; lean_object* v___x_3342_; 
v_a_3341_ = lean_array_uget_borrowed(v_as_3326_, v_i_3328_);
lean_inc(v_snd_3337_);
v___x_3342_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3325_, v_a_3341_, v_snd_3337_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3362_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3362_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3362_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
if (lean_obj_tag(v_a_3343_) == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_a_3343_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3347_);
v___x_3349_ = v___x_3339_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_snd_3337_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3349_);
v___x_3351_ = v___x_3345_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
lean_del_object(v___x_3345_);
lean_dec(v_snd_3337_);
v_a_3354_ = lean_ctor_get(v_a_3343_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v_a_3343_, 1);
v___x_3355_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v_a_3354_);
lean_ctor_set(v___x_3339_, 0, v___x_3355_);
v___x_3357_ = v___x_3339_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_a_3354_);
v___x_3357_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
size_t v___x_3358_; size_t v___x_3359_; 
v___x_3358_ = ((size_t)1ULL);
v___x_3359_ = lean_usize_add(v_i_3328_, v___x_3358_);
v_i_3328_ = v___x_3359_;
v_b_3329_ = v___x_3357_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_del_object(v___x_3339_);
lean_dec(v_snd_3337_);
v_a_3363_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3342_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3342_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3373_, lean_object* v_as_3374_, lean_object* v_sz_3375_, lean_object* v_i_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
size_t v_sz_boxed_3383_; size_t v_i_boxed_3384_; lean_object* v_res_3385_; 
v_sz_boxed_3383_ = lean_unbox_usize(v_sz_3375_);
lean_dec(v_sz_3375_);
v_i_boxed_3384_ = lean_unbox_usize(v_i_3376_);
lean_dec(v_i_3376_);
v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3373_, v_as_3374_, v_sz_boxed_3383_, v_i_boxed_3384_, v_b_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_as_3374_);
lean_dec_ref(v_init_3373_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3386_, lean_object* v_n_3387_, lean_object* v_b_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3386_, v_n_3387_, v_b_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v_n_3387_);
lean_dec_ref(v_init_3386_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3395_, size_t v_sz_3396_, size_t v_i_3397_, lean_object* v_b_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_b_3398_);
return v___x_3405_;
}
else
{
lean_object* v_snd_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3436_; 
v_snd_3406_ = lean_ctor_get(v_b_3398_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_b_3398_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; 
v_unused_3437_ = lean_ctor_get(v_b_3398_, 0);
lean_dec(v_unused_3437_);
v___x_3408_ = v_b_3398_;
v_isShared_3409_ = v_isSharedCheck_3436_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_snd_3406_);
lean_dec(v_b_3398_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3436_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v_a_3412_; lean_object* v_a_3419_; 
v___x_3410_ = lean_box(0);
v_a_3419_ = lean_array_uget_borrowed(v_as_3395_, v_i_3397_);
if (lean_obj_tag(v_a_3419_) == 0)
{
v_a_3412_ = v_snd_3406_;
goto v___jp_3411_;
}
else
{
lean_object* v_val_3420_; uint8_t v___x_3421_; 
v_val_3420_ = lean_ctor_get(v_a_3419_, 0);
v___x_3421_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = l_Lean_LocalDecl_type(v_val_3420_);
v___x_3423_ = l_Lean_Meta_isProp(v___x_3422_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; uint8_t v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = lean_unbox(v_a_3424_);
lean_dec(v_a_3424_);
if (v___x_3425_ == 0)
{
v_a_3412_ = v_snd_3406_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = l_Lean_LocalDecl_fvarId(v_val_3420_);
v___x_3427_ = lean_array_push(v_snd_3406_, v___x_3426_);
v_a_3412_ = v___x_3427_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_del_object(v___x_3408_);
lean_dec(v_snd_3406_);
v_a_3428_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3423_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3423_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
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
else
{
v_a_3412_ = v_snd_3406_;
goto v___jp_3411_;
}
}
v___jp_3411_:
{
lean_object* v___x_3414_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_a_3412_);
lean_ctor_set(v___x_3408_, 0, v___x_3410_);
v___x_3414_ = v___x_3408_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_a_3412_);
v___x_3414_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
size_t v___x_3415_; size_t v___x_3416_; 
v___x_3415_ = ((size_t)1ULL);
v___x_3416_ = lean_usize_add(v_i_3397_, v___x_3415_);
v_i_3397_ = v___x_3416_;
v_b_3398_ = v___x_3414_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3438_, lean_object* v_sz_3439_, lean_object* v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
size_t v_sz_boxed_3447_; size_t v_i_boxed_3448_; lean_object* v_res_3449_; 
v_sz_boxed_3447_ = lean_unbox_usize(v_sz_3439_);
lean_dec(v_sz_3439_);
v_i_boxed_3448_ = lean_unbox_usize(v_i_3440_);
lean_dec(v_i_3440_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3438_, v_sz_boxed_3447_, v_i_boxed_3448_, v_b_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_as_3438_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3450_, size_t v_sz_3451_, size_t v_i_3452_, lean_object* v_b_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_usize_dec_lt(v_i_3452_, v_sz_3451_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_b_3453_);
return v___x_3460_;
}
else
{
lean_object* v_snd_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3491_; 
v_snd_3461_ = lean_ctor_get(v_b_3453_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_b_3453_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v_b_3453_, 0);
lean_dec(v_unused_3492_);
v___x_3463_ = v_b_3453_;
v_isShared_3464_ = v_isSharedCheck_3491_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_snd_3461_);
lean_dec(v_b_3453_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3491_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v_a_3467_; lean_object* v_a_3474_; 
v___x_3465_ = lean_box(0);
v_a_3474_ = lean_array_uget_borrowed(v_as_3450_, v_i_3452_);
if (lean_obj_tag(v_a_3474_) == 0)
{
v_a_3467_ = v_snd_3461_;
goto v___jp_3466_;
}
else
{
lean_object* v_val_3475_; uint8_t v___x_3476_; 
v_val_3475_ = lean_ctor_get(v_a_3474_, 0);
v___x_3476_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = l_Lean_LocalDecl_type(v_val_3475_);
v___x_3478_ = l_Lean_Meta_isProp(v___x_3477_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; uint8_t v___x_3480_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = lean_unbox(v_a_3479_);
lean_dec(v_a_3479_);
if (v___x_3480_ == 0)
{
v_a_3467_ = v_snd_3461_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = l_Lean_LocalDecl_fvarId(v_val_3475_);
v___x_3482_ = lean_array_push(v_snd_3461_, v___x_3481_);
v_a_3467_ = v___x_3482_;
goto v___jp_3466_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_del_object(v___x_3463_);
lean_dec(v_snd_3461_);
v_a_3483_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3478_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3478_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
v_a_3467_ = v_snd_3461_;
goto v___jp_3466_;
}
}
v___jp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_a_3467_);
lean_ctor_set(v___x_3463_, 0, v___x_3465_);
v___x_3469_ = v___x_3463_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_a_3467_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = ((size_t)1ULL);
v___x_3471_ = lean_usize_add(v_i_3452_, v___x_3470_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3450_, v_sz_3451_, v___x_3471_, v___x_3469_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3493_, lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3493_, v_sz_boxed_3502_, v_i_boxed_3503_, v_b_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_as_3493_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3505_, lean_object* v_init_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_root_3512_; lean_object* v_tail_3513_; lean_object* v___x_3514_; 
v_root_3512_ = lean_ctor_get(v_t_3505_, 0);
v_tail_3513_ = lean_ctor_get(v_t_3505_, 1);
lean_inc_ref(v_init_3506_);
v___x_3514_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3506_, v_root_3512_, v_init_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec_ref(v_init_3506_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3551_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3517_ = v___x_3514_;
v_isShared_3518_ = v_isSharedCheck_3551_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3514_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3551_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
if (lean_obj_tag(v_a_3515_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; 
v_a_3519_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v_a_3515_, 1);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v_a_3519_);
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; size_t v_sz_3526_; size_t v___x_3527_; lean_object* v___x_3528_; 
lean_del_object(v___x_3517_);
v_a_3523_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v_a_3515_, 1);
v___x_3524_ = lean_box(0);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v_a_3523_);
v_sz_3526_ = lean_array_size(v_tail_3513_);
v___x_3527_ = ((size_t)0ULL);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3513_, v_sz_3526_, v___x_3527_, v___x_3525_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3542_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_fst_3533_; 
v_fst_3533_ = lean_ctor_get(v_a_3529_, 0);
if (lean_obj_tag(v_fst_3533_) == 0)
{
lean_object* v_snd_3534_; lean_object* v___x_3536_; 
v_snd_3534_ = lean_ctor_get(v_a_3529_, 1);
lean_inc(v_snd_3534_);
lean_dec(v_a_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_snd_3534_);
v___x_3536_ = v___x_3531_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_snd_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
else
{
lean_object* v_val_3538_; lean_object* v___x_3540_; 
lean_inc_ref(v_fst_3533_);
lean_dec(v_a_3529_);
v_val_3538_ = lean_ctor_get(v_fst_3533_, 0);
lean_inc(v_val_3538_);
lean_dec_ref_known(v_fst_3533_, 1);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_val_3538_);
v___x_3540_ = v___x_3531_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_val_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3528_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3528_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
v_a_3552_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3514_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3514_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3560_, lean_object* v_init_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3560_, v_init_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v_t_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_lctx_3573_; lean_object* v_decls_3574_; lean_object* v_result_3575_; lean_object* v___x_3576_; 
v_lctx_3573_ = lean_ctor_get(v_a_3568_, 2);
v_decls_3574_ = lean_ctor_get(v_lctx_3573_, 1);
v_result_3575_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3576_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3574_, v_result_3575_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Meta_getPropHyps(v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3582_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3587_ = l_Lean_MessageData_ofFormat(v___x_3586_);
return v___x_3587_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3590_, lean_object* v___x_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
lean_inc(v___x_3591_);
lean_inc(v_mvarId_3590_);
v___x_3597_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3590_, v___x_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v___x_3598_; 
lean_dec_ref_known(v___x_3597_, 1);
lean_inc(v_mvarId_3590_);
v___x_3598_ = l_Lean_MVarId_getType(v_mvarId_3590_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_box(0);
v___x_3601_ = l_Lean_Meta_synthInstance(v_a_3599_, v___x_3600_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
lean_inc(v_mvarId_3590_);
v___x_3603_ = l_Lean_mkMVar(v_mvarId_3590_);
v___x_3604_ = l_Lean_Meta_isExprDefEq(v___x_3603_, v_a_3602_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3616_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3616_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3616_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
uint8_t v___x_3609_; 
v___x_3609_ = lean_unbox(v_a_3605_);
lean_dec(v_a_3605_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3607_);
v___x_3610_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3611_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3591_, v_mvarId_3590_, v___x_3610_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v___x_3612_ = lean_box(0);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3612_);
v___x_3614_ = v___x_3607_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v_a_3617_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3604_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3604_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v_a_3625_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3601_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3601_);
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
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v_a_3633_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3598_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3598_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3641_, lean_object* v___x_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3641_, v___x_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3652_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3659_, 0, v_mvarId_3652_);
lean_closure_set(v___f_3659_, 1, v___x_3658_);
v___x_3660_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3652_, v___f_3659_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_MVarId_inferInstance(v_mvarId_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_3668_){
_start:
{
switch(lean_obj_tag(v_x_3668_))
{
case 0:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_unsigned_to_nat(0u);
return v___x_3669_;
}
case 1:
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_unsigned_to_nat(1u);
return v___x_3670_;
}
default: 
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_unsigned_to_nat(2u);
return v___x_3671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_3672_);
lean_dec(v_x_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3674_, lean_object* v_k_3675_){
_start:
{
if (lean_obj_tag(v_t_3674_) == 2)
{
lean_object* v_mvarId_3676_; lean_object* v___x_3677_; 
v_mvarId_3676_ = lean_ctor_get(v_t_3674_, 0);
lean_inc(v_mvarId_3676_);
lean_dec_ref_known(v_t_3674_, 1);
v___x_3677_ = lean_apply_1(v_k_3675_, v_mvarId_3676_);
return v___x_3677_;
}
else
{
lean_dec(v_t_3674_);
return v_k_3675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3678_, lean_object* v_ctorIdx_3679_, lean_object* v_t_3680_, lean_object* v_h_3681_, lean_object* v_k_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3680_, v_k_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3684_, lean_object* v_ctorIdx_3685_, lean_object* v_t_3686_, lean_object* v_h_3687_, lean_object* v_k_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3684_, v_ctorIdx_3685_, v_t_3686_, v_h_3687_, v_k_3688_);
lean_dec(v_ctorIdx_3685_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3690_, lean_object* v_closed_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3690_, v_closed_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3693_, lean_object* v_t_3694_, lean_object* v_h_3695_, lean_object* v_closed_3696_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3694_, v_closed_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3698_, lean_object* v_noChange_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3698_, v_noChange_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3701_, lean_object* v_t_3702_, lean_object* v_h_3703_, lean_object* v_noChange_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3702_, v_noChange_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3706_, lean_object* v_modified_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3706_, v_modified_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3709_, lean_object* v_t_3710_, lean_object* v_h_3711_, lean_object* v_modified_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3710_, v_modified_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v_a_3730_; lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_MVarId_getType(v_g_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3736_ = lean_unsigned_to_nat(1u);
v___x_3737_ = lean_mk_empty_array_with_capacity(v___x_3736_);
v___x_3738_ = lean_array_push(v___x_3737_, v_a_3734_);
v___x_3739_ = l_Lean_Meta_mkAppM(v___x_3735_, v___x_3738_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = lean_box(0);
v___x_3742_ = l_Lean_Meta_synthInstance(v_a_3740_, v___x_3741_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3751_; 
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v___x_3742_, 0);
lean_dec(v_unused_3752_);
v___x_3744_ = v___x_3742_;
v_isShared_3745_ = v_isSharedCheck_3751_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v___x_3742_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3751_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3746_ = 1;
v___x_3747_ = lean_box(v___x_3746_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3747_);
v___x_3749_ = v___x_3744_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3753_; 
v_a_3753_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3742_, 1);
v_a_3730_ = v_a_3753_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3754_; 
v_a_3754_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3739_, 1);
v_a_3730_ = v_a_3754_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3733_, 1);
v_a_3730_ = v_a_3755_;
goto v___jp_3729_;
}
v___jp_3723_:
{
if (v___y_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
lean_dec_ref(v___y_3724_);
v___x_3726_ = lean_box(v___y_3725_);
v___x_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
return v___x_3727_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___y_3724_);
return v___x_3728_;
}
}
v___jp_3729_:
{
uint8_t v___x_3731_; 
v___x_3731_ = l_Lean_Exception_isInterrupt(v_a_3730_);
if (v___x_3731_ == 0)
{
uint8_t v___x_3732_; 
lean_inc_ref(v_a_3730_);
v___x_3732_ = l_Lean_Exception_isRuntime(v_a_3730_);
v___y_3724_ = v_a_3730_;
v___y_3725_ = v___x_3732_;
goto v___jp_3723_;
}
else
{
v___y_3724_ = v_a_3730_;
v___y_3725_ = v___x_3731_;
goto v___jp_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_MVarId_isSubsingleton(v_g_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3783_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3780_, v___x_3781_, v___x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3785_;
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
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_debug_terminalTacticsAsSorry = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
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
