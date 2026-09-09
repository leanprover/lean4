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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
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
v___x_106_ = lean_st_ref_put(v_a_92_, v___x_105_);
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
v_options_238_ = lean_ctor_get(v___y_230_, 1);
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
v_ref_255_ = lean_ctor_get(v___y_252_, 4);
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
lean_object* v_nestedMsg_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_msg_359_; lean_object* v_kind_360_; uint8_t v___x_361_; 
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
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_363_ = l_Lean_Name_append(v___x_362_, v_kind_360_);
v___x_364_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_msg_359_);
v___x_365_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_364_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v_kind_360_);
v___x_366_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_359_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_367_, lean_object* v_ex_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_367_, v_ex_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_375_, lean_object* v_tacticName_376_, lean_object* v_ex_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_376_, v_ex_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_384_, lean_object* v_tacticName_385_, lean_object* v_ex_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_384_, v_tacticName_385_, v_ex_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_393_, lean_object* v_i_394_, lean_object* v_k_395_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_array_get_size(v_keys_393_);
v___x_397_ = lean_nat_dec_lt(v_i_394_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v_i_394_);
return v___x_397_;
}
else
{
lean_object* v_k_x27_398_; uint8_t v___x_399_; 
v_k_x27_398_ = lean_array_fget_borrowed(v_keys_393_, v_i_394_);
v___x_399_ = l_Lean_instBEqMVarId_beq(v_k_395_, v_k_x27_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_i_394_, v___x_400_);
lean_dec(v_i_394_);
v_i_394_ = v___x_401_;
goto _start;
}
else
{
lean_dec(v_i_394_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_403_, lean_object* v_i_404_, lean_object* v_k_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_403_, v_i_404_, v_k_405_);
lean_dec(v_k_405_);
lean_dec_ref(v_keys_403_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v_es_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v_j_415_; lean_object* v___x_416_; 
v_es_411_ = lean_ctor_get(v_x_408_, 0);
v___x_412_ = lean_box(2);
v___x_413_ = ((size_t)31ULL);
v___x_414_ = lean_usize_land(v_x_409_, v___x_413_);
v_j_415_ = lean_usize_to_nat(v___x_414_);
v___x_416_ = lean_array_get_borrowed(v___x_412_, v_es_411_, v_j_415_);
lean_dec(v_j_415_);
switch(lean_obj_tag(v___x_416_))
{
case 0:
{
lean_object* v_key_417_; uint8_t v___x_418_; 
v_key_417_ = lean_ctor_get(v___x_416_, 0);
v___x_418_ = l_Lean_instBEqMVarId_beq(v_x_410_, v_key_417_);
return v___x_418_;
}
case 1:
{
lean_object* v_node_419_; size_t v___x_420_; size_t v___x_421_; 
v_node_419_ = lean_ctor_get(v___x_416_, 0);
v___x_420_ = ((size_t)5ULL);
v___x_421_ = lean_usize_shift_right(v_x_409_, v___x_420_);
v_x_408_ = v_node_419_;
v_x_409_ = v___x_421_;
goto _start;
}
default: 
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
else
{
lean_object* v_ks_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_ks_424_ = lean_ctor_get(v_x_408_, 0);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_424_, v___x_425_, v_x_410_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_545__boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_545__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_427_, v_x_545__boxed_430_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_427_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint64_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = l_Lean_instHashableMVarId_hash(v_x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_433_, v___x_436_, v_x_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_x_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_mctx_446_; lean_object* v_eAssignment_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = lean_st_ref_get(v___y_443_);
v_mctx_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc_ref(v_mctx_446_);
lean_dec(v___x_445_);
v_eAssignment_447_ = lean_ctor_get(v_mctx_446_, 8);
lean_inc_ref(v_eAssignment_447_);
lean_dec_ref(v_mctx_446_);
v___x_448_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_447_, v_mvarId_442_);
lean_dec_ref(v_eAssignment_447_);
v___x_449_ = lean_box(v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec(v_mvarId_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_462_ = l_Lean_MessageData_ofFormat(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_464_ = l_Lean_MessageData_note(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_466_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_470_, lean_object* v_tacticName_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v___x_477_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_470_, v_a_473_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; 
v___x_482_ = lean_unbox(v_a_478_);
lean_dec(v_a_478_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_tacticName_471_);
lean_dec(v_mvarId_470_);
v___x_483_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_del_object(v___x_480_);
v___x_487_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_488_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_471_, v_mvarId_470_, v___x_487_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_490_, lean_object* v_tacticName_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_490_, v_tacticName_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_498_, v___y_500_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_mvarId_505_);
return v_res_511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_516_, v_x_517_, v_x_518_);
lean_dec(v_x_518_);
lean_dec_ref(v_x_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_521_, lean_object* v_x_522_, size_t v_x_523_, lean_object* v_x_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_522_, v_x_523_, v_x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_712__boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_x_712__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_531_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_526_, v_x_527_, v_x_712__boxed_530_, v_x_529_);
lean_dec(v_x_529_);
lean_dec_ref(v_x_527_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_533_, lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_heq_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_534_, v_i_537_, v_k_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_540_, lean_object* v_keys_541_, lean_object* v_vals_542_, lean_object* v_heq_543_, lean_object* v_i_544_, lean_object* v_k_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_540_, v_keys_541_, v_vals_542_, v_heq_543_, v_i_544_, v_k_545_);
lean_dec(v_k_545_);
lean_dec_ref(v_vals_542_);
lean_dec_ref(v_keys_541_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_MVarId_getDecl(v_mvarId_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_type_559_; lean_object* v___x_561_; 
v_type_559_ = lean_ctor_get(v_a_555_, 2);
lean_inc_ref(v_type_559_);
lean_dec(v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_type_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_type_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_554_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_554_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_MVarId_getType(v_mvarId_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_Expr_hasMVar(v_e_579_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_e_579_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v_mctx_585_; lean_object* v___x_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v_cache_590_; lean_object* v_zetaDeltaFVarIds_591_; lean_object* v_postponed_592_; lean_object* v_diag_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
v___x_584_ = lean_st_ref_get(v___y_580_);
v_mctx_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc_ref(v_mctx_585_);
lean_dec(v___x_584_);
v___x_586_ = l_Lean_instantiateMVarsCore(v_mctx_585_, v_e_579_);
v_fst_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v___x_586_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v___x_586_);
v___x_589_ = lean_st_ref_take(v___y_580_);
v_cache_590_ = lean_ctor_get(v___x_589_, 1);
v_zetaDeltaFVarIds_591_ = lean_ctor_get(v___x_589_, 2);
v_postponed_592_ = lean_ctor_get(v___x_589_, 3);
v_diag_593_ = lean_ctor_get(v___x_589_, 4);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_603_);
v___x_595_ = v___x_589_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_diag_593_);
lean_inc(v_postponed_592_);
lean_inc(v_zetaDeltaFVarIds_591_);
lean_inc(v_cache_590_);
lean_dec(v___x_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_snd_588_);
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_snd_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_cache_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_zetaDeltaFVarIds_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_postponed_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_diag_593_);
v___x_598_ = v_reuseFailAlloc_601_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_st_ref_put(v___y_580_, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_fst_587_);
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_604_, v___y_605_);
lean_dec(v___y_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_608_, v___y_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_MVarId_getType(v_mvarId_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
lean_inc(v_a_624_);
lean_inc_ref(v_a_623_);
v___x_630_ = lean_whnf(v_a_629_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_631_, v_a_624_);
return v___x_632_;
}
else
{
return v___x_630_;
}
}
else
{
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_MVarId_getType_x27(v_mvarId_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_706_ = 0;
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_708_ = l_Lean_registerTraceClass(v___x_705_, v___x_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_743_, lean_object* v_mvarId_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_744_, v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_752_, lean_object* v_mvarId_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_752_, v_mvarId_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_ks_765_; lean_object* v_vs_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_790_; 
v_ks_765_ = lean_ctor_get(v_x_761_, 0);
v_vs_766_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_790_ == 0)
{
v___x_768_ = v_x_761_;
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_vs_766_);
lean_inc(v_ks_765_);
lean_dec(v_x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_ks_765_);
v___x_771_ = lean_nat_dec_lt(v_x_762_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_x_762_);
v___x_772_ = lean_array_push(v_ks_765_, v_x_763_);
v___x_773_ = lean_array_push(v_vs_766_, v_x_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_773_);
lean_ctor_set(v___x_768_, 0, v___x_772_);
v___x_775_ = v___x_768_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_ks_765_, v_x_762_);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_x_763_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
if (v_isShared_769_ == 0)
{
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_ks_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_vs_766_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_x_762_, v___x_781_);
lean_dec(v_x_762_);
v_x_761_ = v___x_780_;
v_x_762_ = v___x_782_;
goto _start;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_array_fset(v_ks_765_, v_x_762_, v_x_763_);
v___x_786_ = lean_array_fset(v_vs_766_, v_x_762_, v_x_764_);
lean_dec(v_x_762_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_786_);
lean_ctor_set(v___x_768_, 0, v___x_785_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_791_, lean_object* v_k_792_, lean_object* v_v_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_791_, v___x_794_, v_k_792_, v_v_793_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_es_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v_j_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_es_802_ = lean_ctor_get(v_x_797_, 0);
v___x_803_ = ((size_t)31ULL);
v___x_804_ = lean_usize_land(v_x_798_, v___x_803_);
v_j_805_ = lean_usize_to_nat(v___x_804_);
v___x_806_ = lean_array_get_size(v_es_802_);
v___x_807_ = lean_nat_dec_lt(v_j_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_j_805_);
lean_dec(v_x_801_);
lean_dec(v_x_800_);
return v_x_797_;
}
else
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_846_; 
lean_inc_ref(v_es_802_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_x_797_, 0);
lean_dec(v_unused_847_);
v___x_809_ = v_x_797_;
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_v_811_; lean_object* v___x_812_; lean_object* v_xs_x27_813_; lean_object* v___y_815_; 
v_v_811_ = lean_array_fget(v_es_802_, v_j_805_);
v___x_812_ = lean_box(0);
v_xs_x27_813_ = lean_array_fset(v_es_802_, v_j_805_, v___x_812_);
switch(lean_obj_tag(v_v_811_))
{
case 0:
{
lean_object* v_key_820_; lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_key_820_ = lean_ctor_get(v_v_811_, 0);
v_val_821_ = lean_ctor_get(v_v_811_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v_v_811_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_inc(v_key_820_);
lean_dec(v_v_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_instBEqMVarId_beq(v_x_800_, v_key_820_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_823_);
v___x_826_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_820_, v_val_821_, v_x_800_, v_x_801_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___y_815_ = v___x_827_;
goto v___jp_814_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v_val_821_);
lean_dec(v_key_820_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_x_801_);
lean_ctor_set(v___x_823_, 0, v_x_800_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_x_800_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_x_801_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
v___y_815_ = v___x_829_;
goto v___jp_814_;
}
}
}
}
case 1:
{
lean_object* v_node_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_node_832_ = lean_ctor_get(v_v_811_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_v_811_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_node_832_);
lean_dec(v_v_811_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_836_ = ((size_t)5ULL);
v___x_837_ = lean_usize_shift_right(v_x_798_, v___x_836_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_x_799_, v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_832_, v___x_837_, v___x_839_, v_x_800_, v_x_801_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_840_);
v___x_842_ = v___x_834_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v___y_815_ = v___x_842_;
goto v___jp_814_;
}
}
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_x_800_);
lean_ctor_set(v___x_845_, 1, v_x_801_);
v___y_815_ = v___x_845_;
goto v___jp_814_;
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_array_fset(v_xs_x27_813_, v_j_805_, v___y_815_);
lean_dec(v_j_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
else
{
lean_object* v_ks_848_; lean_object* v_vs_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_867_; 
v_ks_848_ = lean_ctor_get(v_x_797_, 0);
v_vs_849_ = lean_ctor_get(v_x_797_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_867_ == 0)
{
v___x_851_ = v_x_797_;
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_vs_849_);
lean_inc(v_ks_848_);
lean_dec(v_x_797_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_ks_848_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_vs_849_);
v___x_854_ = v_reuseFailAlloc_866_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v_newNode_855_; size_t v___x_856_; uint8_t v___x_857_; 
v_newNode_855_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_854_, v_x_800_, v_x_801_);
v___x_856_ = ((size_t)7ULL);
v___x_857_ = lean_usize_dec_le(v___x_856_, v_x_799_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_855_);
v___x_859_ = lean_unsigned_to_nat(4u);
v___x_860_ = lean_nat_dec_lt(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
if (v___x_860_ == 0)
{
lean_object* v_ks_861_; lean_object* v_vs_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_ks_861_ = lean_ctor_get(v_newNode_855_, 0);
lean_inc_ref(v_ks_861_);
v_vs_862_ = lean_ctor_get(v_newNode_855_, 1);
lean_inc_ref(v_vs_862_);
lean_dec_ref(v_newNode_855_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_799_, v_ks_861_, v_vs_862_, v___x_863_, v___x_864_);
lean_dec_ref(v_vs_862_);
lean_dec_ref(v_ks_861_);
return v___x_865_;
}
else
{
return v_newNode_855_;
}
}
else
{
return v_newNode_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_i_871_, lean_object* v_entries_872_){
_start:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_array_get_size(v_keys_869_);
v___x_874_ = lean_nat_dec_lt(v_i_871_, v___x_873_);
if (v___x_874_ == 0)
{
lean_dec(v_i_871_);
return v_entries_872_;
}
else
{
lean_object* v_k_875_; lean_object* v_v_876_; uint64_t v___x_877_; size_t v_h_878_; size_t v___x_879_; lean_object* v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v_h_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_k_875_ = lean_array_fget_borrowed(v_keys_869_, v_i_871_);
v_v_876_ = lean_array_fget_borrowed(v_vals_870_, v_i_871_);
v___x_877_ = l_Lean_instHashableMVarId_hash(v_k_875_);
v_h_878_ = lean_uint64_to_usize(v___x_877_);
v___x_879_ = ((size_t)5ULL);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_sub(v_depth_868_, v___x_881_);
v___x_883_ = lean_usize_mul(v___x_879_, v___x_882_);
v_h_884_ = lean_usize_shift_right(v_h_878_, v___x_883_);
v___x_885_ = lean_nat_add(v_i_871_, v___x_880_);
lean_dec(v_i_871_);
lean_inc(v_v_876_);
lean_inc(v_k_875_);
v___x_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_872_, v_h_884_, v_depth_868_, v_k_875_, v_v_876_);
v_i_871_ = v___x_885_;
v_entries_872_ = v___x_886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_888_, lean_object* v_keys_889_, lean_object* v_vals_890_, lean_object* v_i_891_, lean_object* v_entries_892_){
_start:
{
size_t v_depth_boxed_893_; lean_object* v_res_894_; 
v_depth_boxed_893_ = lean_unbox_usize(v_depth_888_);
lean_dec(v_depth_888_);
v_res_894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_893_, v_keys_889_, v_vals_890_, v_i_891_, v_entries_892_);
lean_dec_ref(v_vals_890_);
lean_dec_ref(v_keys_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_1015__boxed_900_; size_t v_x_1016__boxed_901_; lean_object* v_res_902_; 
v_x_1015__boxed_900_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_x_1016__boxed_901_ = lean_unbox_usize(v_x_897_);
lean_dec(v_x_897_);
v_res_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_895_, v_x_1015__boxed_900_, v_x_1016__boxed_901_, v_x_898_, v_x_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
uint64_t v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_906_ = l_Lean_instHashableMVarId_hash(v_x_904_);
v___x_907_ = lean_uint64_to_usize(v___x_906_);
v___x_908_ = ((size_t)1ULL);
v___x_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_903_, v___x_907_, v___x_908_, v_x_904_, v_x_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_910_, lean_object* v_val_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_mctx_915_; lean_object* v_cache_916_; lean_object* v_zetaDeltaFVarIds_917_; lean_object* v_postponed_918_; lean_object* v_diag_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_948_; 
v___x_914_ = lean_st_ref_take(v___y_912_);
v_mctx_915_ = lean_ctor_get(v___x_914_, 0);
v_cache_916_ = lean_ctor_get(v___x_914_, 1);
v_zetaDeltaFVarIds_917_ = lean_ctor_get(v___x_914_, 2);
v_postponed_918_ = lean_ctor_get(v___x_914_, 3);
v_diag_919_ = lean_ctor_get(v___x_914_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_948_ == 0)
{
v___x_921_ = v___x_914_;
v_isShared_922_ = v_isSharedCheck_948_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_diag_919_);
lean_inc(v_postponed_918_);
lean_inc(v_zetaDeltaFVarIds_917_);
lean_inc(v_cache_916_);
lean_inc(v_mctx_915_);
lean_dec(v___x_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_948_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_depth_923_; lean_object* v_levelAssignDepth_924_; lean_object* v_lmvarCounter_925_; lean_object* v_mvarCounter_926_; lean_object* v_lDecls_927_; lean_object* v_decls_928_; lean_object* v_userNames_929_; lean_object* v_lAssignment_930_; lean_object* v_eAssignment_931_; lean_object* v_dAssignment_932_; lean_object* v_instanceTypedMVars_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_depth_923_ = lean_ctor_get(v_mctx_915_, 0);
v_levelAssignDepth_924_ = lean_ctor_get(v_mctx_915_, 1);
v_lmvarCounter_925_ = lean_ctor_get(v_mctx_915_, 2);
v_mvarCounter_926_ = lean_ctor_get(v_mctx_915_, 3);
v_lDecls_927_ = lean_ctor_get(v_mctx_915_, 4);
v_decls_928_ = lean_ctor_get(v_mctx_915_, 5);
v_userNames_929_ = lean_ctor_get(v_mctx_915_, 6);
v_lAssignment_930_ = lean_ctor_get(v_mctx_915_, 7);
v_eAssignment_931_ = lean_ctor_get(v_mctx_915_, 8);
v_dAssignment_932_ = lean_ctor_get(v_mctx_915_, 9);
v_instanceTypedMVars_933_ = lean_ctor_get(v_mctx_915_, 10);
v_isSharedCheck_947_ = !lean_is_exclusive(v_mctx_915_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_mctx_915_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_instanceTypedMVars_933_);
lean_inc(v_dAssignment_932_);
lean_inc(v_eAssignment_931_);
lean_inc(v_lAssignment_930_);
lean_inc(v_userNames_929_);
lean_inc(v_decls_928_);
lean_inc(v_lDecls_927_);
lean_inc(v_mvarCounter_926_);
lean_inc(v_lmvarCounter_925_);
lean_inc(v_levelAssignDepth_924_);
lean_inc(v_depth_923_);
lean_dec(v_mctx_915_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_931_, v_mvarId_910_, v_val_911_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 8, v___x_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_depth_923_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_levelAssignDepth_924_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_lmvarCounter_925_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_mvarCounter_926_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_lDecls_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_decls_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_userNames_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_lAssignment_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 9, v_dAssignment_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 10, v_instanceTypedMVars_933_);
v___x_939_ = v_reuseFailAlloc_946_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_939_);
v___x_941_ = v___x_921_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_cache_916_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_zetaDeltaFVarIds_917_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_postponed_918_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_diag_919_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_st_ref_put(v___y_912_, v___x_941_);
v___x_943_ = lean_box(0);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_949_, lean_object* v_val_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_949_, v_val_950_, v___y_951_);
lean_dec(v___y_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_954_, lean_object* v___x_955_, uint8_t v_synthetic_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
lean_inc(v_mvarId_954_);
v___x_962_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_954_, v___x_955_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_963_; 
lean_dec_ref_known(v___x_962_, 1);
lean_inc(v_mvarId_954_);
v___x_963_ = l_Lean_MVarId_getType(v_mvarId_954_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; uint8_t v___x_965_; lean_object* v___x_966_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = 1;
v___x_966_ = l_Lean_Meta_mkLabeledSorry(v_a_964_, v_synthetic_956_, v___x_965_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_954_, v_a_967_, v___y_958_);
return v___x_968_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_mvarId_954_);
v_a_969_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_966_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_966_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_mvarId_954_);
v_a_977_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_963_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_963_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_dec(v_mvarId_954_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_985_, lean_object* v___x_986_, lean_object* v_synthetic_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v_synthetic_boxed_993_; lean_object* v_res_994_; 
v_synthetic_boxed_993_ = lean_unbox(v_synthetic_987_);
v_res_994_ = l_Lean_MVarId_admit___lam__0(v_mvarId_985_, v___x_986_, v_synthetic_boxed_993_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_998_, uint8_t v_synthetic_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; 
v___x_1005_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1006_ = lean_box(v_synthetic_999_);
lean_inc(v_mvarId_998_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1007_, 0, v_mvarId_998_);
lean_closure_set(v___f_1007_, 1, v___x_1005_);
lean_closure_set(v___f_1007_, 2, v___x_1006_);
v___x_1008_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_998_, v___f_1007_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1009_, lean_object* v_synthetic_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
uint8_t v_synthetic_boxed_1016_; lean_object* v_res_1017_; 
v_synthetic_boxed_1016_ = lean_unbox(v_synthetic_1010_);
v_res_1017_ = l_Lean_MVarId_admit(v_mvarId_1009_, v_synthetic_boxed_1016_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1018_, lean_object* v_val_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1018_, v_val_1019_, v___y_1021_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1026_, lean_object* v_val_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1026_, v_val_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1035_, v_x_1036_, v_x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, size_t v_x_1041_, size_t v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1040_, v_x_1041_, v_x_1042_, v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
size_t v_x_1336__boxed_1052_; size_t v_x_1337__boxed_1053_; lean_object* v_res_1054_; 
v_x_1336__boxed_1052_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_x_1337__boxed_1053_ = lean_unbox_usize(v_x_1049_);
lean_dec(v_x_1049_);
v_res_1054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1046_, v_x_1047_, v_x_1336__boxed_1052_, v_x_1337__boxed_1053_, v_x_1050_, v_x_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1055_, lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1056_, v_k_1057_, v_v_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1060_, size_t v_depth_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_entries_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1061_, v_keys_1062_, v_vals_1063_, v_i_1065_, v_entries_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; 
lean_inc(v_mvarId_1083_);
v___x_1089_ = l_Lean_MVarId_getType(v_mvarId_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = l_Lean_Expr_headBeta(v_a_1090_);
v___x_1092_ = l_Lean_MVarId_setType___redArg(v_mvarId_1083_, v___x_1091_, v_a_1085_);
return v___x_1092_;
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec(v_mvarId_1083_);
v_a_1093_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1089_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1089_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_MVarId_headBetaType(v_mvarId_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
uint8_t v___x_1110_; 
v___x_1110_ = 0;
return v___x_1110_;
}
else
{
lean_object* v_key_1111_; lean_object* v_tail_1112_; uint8_t v___x_1113_; 
v_key_1111_ = lean_ctor_get(v_x_1109_, 0);
v_tail_1112_ = lean_ctor_get(v_x_1109_, 2);
v___x_1113_ = l_Lean_instBEqFVarId_beq(v_key_1111_, v_a_1108_);
if (v___x_1113_ == 0)
{
v_x_1109_ = v_tail_1112_;
goto _start;
}
else
{
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
uint8_t v_res_1117_; lean_object* v_r_1118_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec(v_a_1115_);
v_r_1118_ = lean_box(v_res_1117_);
return v_r_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
if (lean_obj_tag(v_x_1120_) == 0)
{
return v_x_1120_;
}
else
{
lean_object* v_key_1121_; lean_object* v_value_1122_; lean_object* v_tail_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v_key_1121_ = lean_ctor_get(v_x_1120_, 0);
v_value_1122_ = lean_ctor_get(v_x_1120_, 1);
v_tail_1123_ = lean_ctor_get(v_x_1120_, 2);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1120_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1125_ = v_x_1120_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_tail_1123_);
lean_inc(v_value_1122_);
lean_inc(v_key_1121_);
lean_dec(v_x_1120_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_instBEqFVarId_beq(v_key_1121_, v_a_1119_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1119_, v_tail_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 2, v___x_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_key_1121_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_value_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_del_object(v___x_1125_);
lean_dec(v_value_1122_);
lean_dec(v_key_1121_);
return v_tail_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1133_, v_x_1134_);
lean_dec(v_a_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_size_1138_; lean_object* v_buckets_1139_; lean_object* v___x_1140_; uint64_t v___x_1141_; uint64_t v___x_1142_; uint64_t v___x_1143_; uint64_t v_fold_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; size_t v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; lean_object* v_bkt_1153_; uint8_t v___x_1154_; 
v_size_1138_ = lean_ctor_get(v_m_1136_, 0);
v_buckets_1139_ = lean_ctor_get(v_m_1136_, 1);
v___x_1140_ = lean_array_get_size(v_buckets_1139_);
v___x_1141_ = l_Lean_instHashableFVarId_hash(v_a_1137_);
v___x_1142_ = 32ULL;
v___x_1143_ = lean_uint64_shift_right(v___x_1141_, v___x_1142_);
v_fold_1144_ = lean_uint64_xor(v___x_1141_, v___x_1143_);
v___x_1145_ = 16ULL;
v___x_1146_ = lean_uint64_shift_right(v_fold_1144_, v___x_1145_);
v___x_1147_ = lean_uint64_xor(v_fold_1144_, v___x_1146_);
v___x_1148_ = lean_uint64_to_usize(v___x_1147_);
v___x_1149_ = lean_usize_of_nat(v___x_1140_);
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_sub(v___x_1149_, v___x_1150_);
v___x_1152_ = lean_usize_land(v___x_1148_, v___x_1151_);
v_bkt_1153_ = lean_array_uget_borrowed(v_buckets_1139_, v___x_1152_);
v___x_1154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1137_, v_bkt_1153_);
if (v___x_1154_ == 0)
{
return v_m_1136_;
}
else
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1167_; 
lean_inc(v_bkt_1153_);
lean_inc_ref(v_buckets_1139_);
lean_inc(v_size_1138_);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_m_1136_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1168_ = lean_ctor_get(v_m_1136_, 1);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_m_1136_, 0);
lean_dec(v_unused_1169_);
v___x_1156_ = v_m_1136_;
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v_m_1136_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v_buckets_x27_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1158_ = lean_box(0);
v_buckets_x27_1159_ = lean_array_uset(v_buckets_1139_, v___x_1152_, v___x_1158_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_sub(v_size_1138_, v___x_1160_);
lean_dec(v_size_1138_);
v___x_1162_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1137_, v_bkt_1153_);
v___x_1163_ = lean_array_uset(v_buckets_x27_1159_, v___x_1152_, v___x_1162_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1163_);
lean_ctor_set(v___x_1156_, 0, v___x_1161_);
v___x_1165_ = v___x_1156_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1170_, v_a_1171_);
lean_dec(v_a_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1180_ = lean_st_ref_take(v___y_1174_);
v___x_1181_ = l_Lean_Expr_fvarId_x21(v_e_1173_);
v___x_1182_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1180_, v___x_1181_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_st_ref_put(v___y_1174_, v___x_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v_e_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_st_ref_get(v___y_1195_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_visited_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; size_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1214_ = lean_st_ref_get(v_a_1212_);
v_visited_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_ref(v_visited_1215_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_ptr_addr(v_e_1211_);
v___x_1217_ = ((size_t)8191ULL);
v___x_1218_ = lean_usize_mod(v___x_1216_, v___x_1217_);
v___x_1219_ = lean_array_uget(v_visited_1215_, v___x_1218_);
lean_dec_ref(v_visited_1215_);
v___x_1220_ = lean_ptr_addr(v___x_1219_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_usize_dec_eq(v___x_1220_, v___x_1216_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v_visited_1223_; lean_object* v_checked_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1235_; 
v___x_1222_ = lean_st_ref_take(v_a_1212_);
v_visited_1223_ = lean_ctor_get(v___x_1222_, 0);
v_checked_1224_ = lean_ctor_get(v___x_1222_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1226_ = v___x_1222_;
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_checked_1224_);
lean_inc(v_visited_1223_);
lean_dec(v___x_1222_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = lean_array_uset(v_visited_1223_, v___x_1218_, v_e_1211_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_checked_1224_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_st_ref_put(v_a_1212_, v___x_1230_);
v___x_1232_ = lean_box(v___x_1221_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v_e_1211_);
v___x_1236_ = lean_box(v___x_1221_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1238_, v_a_1239_);
lean_dec(v_a_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = 0;
return v___x_1244_;
}
else
{
lean_object* v_key_1245_; lean_object* v_tail_1246_; uint8_t v___x_1247_; 
v_key_1245_ = lean_ctor_get(v_x_1243_, 0);
v_tail_1246_ = lean_ctor_get(v_x_1243_, 2);
v___x_1247_ = lean_expr_eqv(v_key_1245_, v_a_1242_);
if (v___x_1247_ == 0)
{
v_x_1243_ = v_tail_1246_;
goto _start;
}
else
{
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1249_, v_x_1250_);
lean_dec(v_x_1250_);
lean_dec_ref(v_a_1249_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
return v_x_1253_;
}
else
{
lean_object* v_key_1255_; lean_object* v_value_1256_; lean_object* v_tail_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1280_; 
v_key_1255_ = lean_ctor_get(v_x_1254_, 0);
v_value_1256_ = lean_ctor_get(v_x_1254_, 1);
v_tail_1257_ = lean_ctor_get(v_x_1254_, 2);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1259_ = v_x_1254_;
v_isShared_1260_ = v_isSharedCheck_1280_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_tail_1257_);
lean_inc(v_value_1256_);
lean_inc(v_key_1255_);
lean_dec(v_x_1254_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1280_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; uint64_t v___x_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v_fold_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1261_ = lean_array_get_size(v_x_1253_);
v___x_1262_ = l_Lean_Expr_hash(v_key_1255_);
v___x_1263_ = 32ULL;
v___x_1264_ = lean_uint64_shift_right(v___x_1262_, v___x_1263_);
v_fold_1265_ = lean_uint64_xor(v___x_1262_, v___x_1264_);
v___x_1266_ = 16ULL;
v___x_1267_ = lean_uint64_shift_right(v_fold_1265_, v___x_1266_);
v___x_1268_ = lean_uint64_xor(v_fold_1265_, v___x_1267_);
v___x_1269_ = lean_uint64_to_usize(v___x_1268_);
v___x_1270_ = lean_usize_of_nat(v___x_1261_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_sub(v___x_1270_, v___x_1271_);
v___x_1273_ = lean_usize_land(v___x_1269_, v___x_1272_);
v___x_1274_ = lean_array_uget_borrowed(v_x_1253_, v___x_1273_);
lean_inc(v___x_1274_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 2, v___x_1274_);
v___x_1276_ = v___x_1259_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_key_1255_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_value_1256_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_array_uset(v_x_1253_, v___x_1273_, v___x_1276_);
v_x_1253_ = v___x_1277_;
v_x_1254_ = v_tail_1257_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1281_, lean_object* v_source_1282_, lean_object* v_target_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v_source_1282_);
v___x_1285_ = lean_nat_dec_lt(v_i_1281_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec_ref(v_source_1282_);
lean_dec(v_i_1281_);
return v_target_1283_;
}
else
{
lean_object* v_es_1286_; lean_object* v___x_1287_; lean_object* v_source_1288_; lean_object* v_target_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_es_1286_ = lean_array_fget(v_source_1282_, v_i_1281_);
v___x_1287_ = lean_box(0);
v_source_1288_ = lean_array_fset(v_source_1282_, v_i_1281_, v___x_1287_);
v_target_1289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1283_, v_es_1286_);
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_add(v_i_1281_, v___x_1290_);
lean_dec(v_i_1281_);
v_i_1281_ = v___x_1291_;
v_source_1282_ = v_source_1288_;
v_target_1283_ = v_target_1289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_nbuckets_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1294_ = lean_array_get_size(v_data_1293_);
v___x_1295_ = lean_unsigned_to_nat(2u);
v_nbuckets_1296_ = lean_nat_mul(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_mk_array(v_nbuckets_1296_, v___x_1298_);
v___x_1300_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1297_, v_data_1293_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_){
_start:
{
lean_object* v_size_1304_; lean_object* v_buckets_1305_; lean_object* v___x_1306_; uint64_t v___x_1307_; uint64_t v___x_1308_; uint64_t v___x_1309_; uint64_t v_fold_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v_bkt_1319_; uint8_t v___x_1320_; 
v_size_1304_ = lean_ctor_get(v_m_1301_, 0);
v_buckets_1305_ = lean_ctor_get(v_m_1301_, 1);
v___x_1306_ = lean_array_get_size(v_buckets_1305_);
v___x_1307_ = l_Lean_Expr_hash(v_a_1302_);
v___x_1308_ = 32ULL;
v___x_1309_ = lean_uint64_shift_right(v___x_1307_, v___x_1308_);
v_fold_1310_ = lean_uint64_xor(v___x_1307_, v___x_1309_);
v___x_1311_ = 16ULL;
v___x_1312_ = lean_uint64_shift_right(v_fold_1310_, v___x_1311_);
v___x_1313_ = lean_uint64_xor(v_fold_1310_, v___x_1312_);
v___x_1314_ = lean_uint64_to_usize(v___x_1313_);
v___x_1315_ = lean_usize_of_nat(v___x_1306_);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_sub(v___x_1315_, v___x_1316_);
v___x_1318_ = lean_usize_land(v___x_1314_, v___x_1317_);
v_bkt_1319_ = lean_array_uget_borrowed(v_buckets_1305_, v___x_1318_);
v___x_1320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1302_, v_bkt_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1341_; 
lean_inc_ref(v_buckets_1305_);
lean_inc(v_size_1304_);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_m_1301_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; lean_object* v_unused_1343_; 
v_unused_1342_ = lean_ctor_get(v_m_1301_, 1);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v_m_1301_, 0);
lean_dec(v_unused_1343_);
v___x_1322_ = v_m_1301_;
v_isShared_1323_ = v_isSharedCheck_1341_;
goto v_resetjp_1321_;
}
else
{
lean_dec(v_m_1301_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1341_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v_size_x27_1325_; lean_object* v___x_1326_; lean_object* v_buckets_x27_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1324_ = lean_unsigned_to_nat(1u);
v_size_x27_1325_ = lean_nat_add(v_size_1304_, v___x_1324_);
lean_dec(v_size_1304_);
lean_inc(v_bkt_1319_);
v___x_1326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1326_, 0, v_a_1302_);
lean_ctor_set(v___x_1326_, 1, v_b_1303_);
lean_ctor_set(v___x_1326_, 2, v_bkt_1319_);
v_buckets_x27_1327_ = lean_array_uset(v_buckets_1305_, v___x_1318_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(4u);
v___x_1329_ = lean_nat_mul(v_size_x27_1325_, v___x_1328_);
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_nat_div(v___x_1329_, v___x_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_array_get_size(v_buckets_x27_1327_);
v___x_1333_ = lean_nat_dec_le(v___x_1331_, v___x_1332_);
lean_dec(v___x_1331_);
if (v___x_1333_ == 0)
{
lean_object* v_val_1334_; lean_object* v___x_1336_; 
v_val_1334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1327_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v_val_1334_);
lean_ctor_set(v___x_1322_, 0, v_size_x27_1325_);
v___x_1336_ = v___x_1322_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_size_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_val_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v___x_1339_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v_buckets_x27_1327_);
lean_ctor_set(v___x_1322_, 0, v_size_x27_1325_);
v___x_1339_ = v___x_1322_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_size_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_buckets_x27_1327_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_dec(v_b_1303_);
lean_dec_ref(v_a_1302_);
return v_m_1301_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_buckets_1346_; lean_object* v___x_1347_; uint64_t v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v_fold_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_buckets_1346_ = lean_ctor_get(v_m_1344_, 1);
v___x_1347_ = lean_array_get_size(v_buckets_1346_);
v___x_1348_ = l_Lean_Expr_hash(v_a_1345_);
v___x_1349_ = 32ULL;
v___x_1350_ = lean_uint64_shift_right(v___x_1348_, v___x_1349_);
v_fold_1351_ = lean_uint64_xor(v___x_1348_, v___x_1350_);
v___x_1352_ = 16ULL;
v___x_1353_ = lean_uint64_shift_right(v_fold_1351_, v___x_1352_);
v___x_1354_ = lean_uint64_xor(v_fold_1351_, v___x_1353_);
v___x_1355_ = lean_uint64_to_usize(v___x_1354_);
v___x_1356_ = lean_usize_of_nat(v___x_1347_);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_sub(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_usize_land(v___x_1355_, v___x_1358_);
v___x_1360_ = lean_array_uget_borrowed(v_buckets_1346_, v___x_1359_);
v___x_1361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1345_, v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1362_, lean_object* v_a_1363_){
_start:
{
uint8_t v_res_1364_; lean_object* v_r_1365_; 
v_res_1364_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1362_, v_a_1363_);
lean_dec_ref(v_a_1363_);
lean_dec_ref(v_m_1362_);
v_r_1365_ = lean_box(v_res_1364_);
return v_r_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_checked_1370_; uint8_t v___x_1371_; 
v___x_1369_ = lean_st_ref_get(v_a_1367_);
v_checked_1370_ = lean_ctor_get(v___x_1369_, 1);
lean_inc_ref(v_checked_1370_);
lean_dec(v___x_1369_);
v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1370_, v_e_1366_);
lean_dec_ref(v_checked_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v_visited_1373_; lean_object* v_checked_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1386_; 
v___x_1372_ = lean_st_ref_take(v_a_1367_);
v_visited_1373_ = lean_ctor_get(v___x_1372_, 0);
v_checked_1374_ = lean_ctor_get(v___x_1372_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1376_ = v___x_1372_;
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_checked_1374_);
lean_inc(v_visited_1373_);
lean_dec(v___x_1372_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1374_, v_e_1366_, v___x_1378_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v___x_1379_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_visited_1373_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_st_ref_put(v_a_1367_, v___x_1381_);
v___x_1383_ = lean_box(v___x_1371_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec_ref(v_e_1366_);
v___x_1387_ = lean_box(v___x_1371_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1389_, lean_object* v_a_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1389_, v_a_1390_);
lean_dec(v_a_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1393_, lean_object* v_f_1394_, uint8_t v_stopWhenVisited_1395_, lean_object* v_e_1396_, lean_object* v_a_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v_d_1410_; lean_object* v_b_1411_; lean_object* v___y_1412_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___x_1442_; 
lean_inc_ref(v_e_1396_);
v___x_1442_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1475_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1475_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1475_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_unbox(v_a_1443_);
lean_dec(v_a_1443_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
lean_del_object(v___x_1445_);
lean_inc_ref(v_p_1393_);
lean_inc_ref(v_e_1396_);
v___x_1448_ = lean_apply_1(v_p_1393_, v_e_1396_);
v___x_1449_ = lean_unbox(v___x_1448_);
if (v___x_1449_ == 0)
{
v___y_1416_ = v_a_1397_;
v___y_1417_ = v___y_1398_;
v___y_1418_ = v___y_1399_;
v___y_1419_ = v___y_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1450_; 
lean_inc_ref(v_e_1396_);
v___x_1450_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; uint8_t v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = lean_unbox(v_a_1451_);
lean_dec(v_a_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_inc_ref(v_f_1394_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v_e_1396_);
v___x_1453_ = lean_apply_7(v_f_1394_, v_e_1396_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, lean_box(0));
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1461_; 
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1453_, 0);
lean_dec(v_unused_1462_);
v___x_1455_ = v___x_1453_;
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v___x_1453_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1461_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
if (v_stopWhenVisited_1395_ == 0)
{
lean_del_object(v___x_1455_);
v___y_1416_ = v_a_1397_;
v___y_1417_ = v___y_1398_;
v___y_1418_ = v___y_1399_;
v___y_1419_ = v___y_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
v___x_1457_ = lean_box(0);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
return v___x_1453_;
}
}
else
{
v___y_1416_ = v_a_1397_;
v___y_1417_ = v___y_1398_;
v___y_1418_ = v___y_1399_;
v___y_1419_ = v___y_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
goto v___jp_1415_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
v_a_1463_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1450_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1450_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
v___x_1471_ = lean_box(0);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1471_);
v___x_1473_ = v___x_1445_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
v_a_1476_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1442_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1442_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
v___jp_1404_:
{
lean_object* v___x_1413_; 
lean_inc_ref(v_f_1394_);
lean_inc_ref(v_p_1393_);
v___x_1413_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1393_, v_f_1394_, v_stopWhenVisited_1395_, v_d_1410_, v___y_1412_, v___y_1406_, v___y_1408_, v___y_1407_, v___y_1405_, v___y_1409_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref_known(v___x_1413_, 1);
v_e_1396_ = v_b_1411_;
v_a_1397_ = v___y_1412_;
v___y_1398_ = v___y_1406_;
v___y_1399_ = v___y_1408_;
v___y_1400_ = v___y_1407_;
v___y_1401_ = v___y_1405_;
v___y_1402_ = v___y_1409_;
goto _start;
}
else
{
lean_dec_ref(v_b_1411_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
return v___x_1413_;
}
}
v___jp_1415_:
{
switch(lean_obj_tag(v_e_1396_))
{
case 7:
{
lean_object* v_binderType_1422_; lean_object* v_body_1423_; 
v_binderType_1422_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_binderType_1422_);
v_body_1423_ = lean_ctor_get(v_e_1396_, 2);
lean_inc_ref(v_body_1423_);
lean_dec_ref_known(v_e_1396_, 3);
v___y_1405_ = v___y_1420_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1419_;
v___y_1408_ = v___y_1418_;
v___y_1409_ = v___y_1421_;
v_d_1410_ = v_binderType_1422_;
v_b_1411_ = v_body_1423_;
v___y_1412_ = v___y_1416_;
goto v___jp_1404_;
}
case 6:
{
lean_object* v_binderType_1424_; lean_object* v_body_1425_; 
v_binderType_1424_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_binderType_1424_);
v_body_1425_ = lean_ctor_get(v_e_1396_, 2);
lean_inc_ref(v_body_1425_);
lean_dec_ref_known(v_e_1396_, 3);
v___y_1405_ = v___y_1420_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1419_;
v___y_1408_ = v___y_1418_;
v___y_1409_ = v___y_1421_;
v_d_1410_ = v_binderType_1424_;
v_b_1411_ = v_body_1425_;
v___y_1412_ = v___y_1416_;
goto v___jp_1404_;
}
case 8:
{
lean_object* v_type_1426_; lean_object* v_value_1427_; lean_object* v_body_1428_; lean_object* v___x_1429_; 
v_type_1426_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_type_1426_);
v_value_1427_ = lean_ctor_get(v_e_1396_, 2);
lean_inc_ref(v_value_1427_);
v_body_1428_ = lean_ctor_get(v_e_1396_, 3);
lean_inc_ref(v_body_1428_);
lean_dec_ref_known(v_e_1396_, 4);
lean_inc_ref(v_f_1394_);
lean_inc_ref(v_p_1393_);
v___x_1429_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1393_, v_f_1394_, v_stopWhenVisited_1395_, v_type_1426_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v___x_1430_; 
lean_dec_ref_known(v___x_1429_, 1);
lean_inc_ref(v_f_1394_);
lean_inc_ref(v_p_1393_);
v___x_1430_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1393_, v_f_1394_, v_stopWhenVisited_1395_, v_value_1427_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_dec_ref_known(v___x_1430_, 1);
v_e_1396_ = v_body_1428_;
v_a_1397_ = v___y_1416_;
v___y_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
goto _start;
}
else
{
lean_dec_ref(v_body_1428_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
return v___x_1430_;
}
}
else
{
lean_dec_ref(v_body_1428_);
lean_dec_ref(v_value_1427_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
return v___x_1429_;
}
}
case 5:
{
lean_object* v_fn_1432_; lean_object* v_arg_1433_; lean_object* v___x_1434_; 
v_fn_1432_ = lean_ctor_get(v_e_1396_, 0);
lean_inc_ref(v_fn_1432_);
v_arg_1433_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_arg_1433_);
lean_dec_ref_known(v_e_1396_, 2);
lean_inc_ref(v_f_1394_);
lean_inc_ref(v_p_1393_);
v___x_1434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1393_, v_f_1394_, v_stopWhenVisited_1395_, v_fn_1432_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
v_e_1396_ = v_arg_1433_;
v_a_1397_ = v___y_1416_;
v___y_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1433_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
return v___x_1434_;
}
}
case 10:
{
lean_object* v_expr_1436_; 
v_expr_1436_ = lean_ctor_get(v_e_1396_, 1);
lean_inc_ref(v_expr_1436_);
lean_dec_ref_known(v_e_1396_, 2);
v_e_1396_ = v_expr_1436_;
v_a_1397_ = v___y_1416_;
v___y_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
goto _start;
}
case 11:
{
lean_object* v_struct_1438_; 
v_struct_1438_ = lean_ctor_get(v_e_1396_, 2);
lean_inc_ref(v_struct_1438_);
lean_dec_ref_known(v_e_1396_, 3);
v_e_1396_ = v_struct_1438_;
v_a_1397_ = v___y_1416_;
v___y_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
goto _start;
}
default: 
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec_ref(v_e_1396_);
lean_dec_ref(v_f_1394_);
lean_dec_ref(v_p_1393_);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1484_, lean_object* v_f_1485_, lean_object* v_stopWhenVisited_1486_, lean_object* v_e_1487_, lean_object* v_a_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1495_; lean_object* v_res_1496_; 
v_stopWhenVisited_boxed_1495_ = lean_unbox(v_stopWhenVisited_1486_);
v_res_1496_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1484_, v_f_1485_, v_stopWhenVisited_boxed_1495_, v_e_1487_, v_a_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v_a_1488_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1497_, lean_object* v_f_1498_, lean_object* v_e_1499_, uint8_t v_stopWhenVisited_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = l_Lean_ForEachExprWhere_initCache;
v___x_1508_ = lean_st_mk_ref(v___x_1507_);
v___x_1509_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1497_, v_f_1498_, v_stopWhenVisited_1500_, v_e_1499_, v___x_1508_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_st_ref_get(v___x_1508_);
lean_dec(v___x_1508_);
lean_dec(v___x_1514_);
if (v_isShared_1513_ == 0)
{
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1510_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_dec(v___x_1508_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1519_, lean_object* v_f_1520_, lean_object* v_e_1521_, lean_object* v_stopWhenVisited_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1529_; lean_object* v_res_1530_; 
v_stopWhenVisited_boxed_1529_ = lean_unbox(v_stopWhenVisited_1522_);
v_res_1530_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1519_, v_f_1520_, v_e_1521_, v_stopWhenVisited_boxed_1529_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1532_, lean_object* v___f_1533_, uint8_t v___x_1534_, lean_object* v_e_1535_, lean_object* v_candidates_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1535_, v___y_1538_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___y_1546_; uint8_t v___x_1556_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = lean_st_mk_ref(v_candidates_1536_);
v___x_1556_ = l_Lean_Expr_hasFVar(v_a_1543_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v_a_1543_);
lean_dec_ref(v___f_1533_);
v___x_1557_ = lean_box(0);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___x_1544_);
v___x_1558_ = lean_apply_7(v___f_1532_, v___x_1557_, v___x_1544_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, lean_box(0));
v___y_1546_ = v___x_1558_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1560_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1559_, v___f_1533_, v_a_1543_, v___x_1534_, v___x_1544_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
lean_inc(v___x_1544_);
v___x_1562_ = lean_apply_7(v___f_1532_, v_a_1561_, v___x_1544_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, lean_box(0));
v___y_1546_ = v___x_1562_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v___x_1544_);
lean_dec_ref(v___f_1532_);
v_a_1563_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1560_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1560_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
v___jp_1545_:
{
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_a_1547_ = lean_ctor_get(v___y_1546_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___y_1546_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1549_ = v___y_1546_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___y_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_st_ref_get(v___x_1544_);
lean_dec(v___x_1544_);
lean_dec(v___x_1551_);
if (v_isShared_1550_ == 0)
{
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1547_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_dec(v___x_1544_);
return v___y_1546_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_candidates_1536_);
lean_dec_ref(v___f_1533_);
lean_dec_ref(v___f_1532_);
v_a_1571_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1542_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1542_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1579_, lean_object* v___f_1580_, lean_object* v___x_1581_, lean_object* v_e_1582_, lean_object* v_candidates_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v___x_16885__boxed_1589_; lean_object* v_res_1590_; 
v___x_16885__boxed_1589_ = lean_unbox(v___x_1581_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1579_, v___f_1580_, v___x_16885__boxed_1589_, v_e_1582_, v_candidates_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_____r_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_st_ref_get(v___y_1592_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_____r_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_e_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = lean_st_ref_take(v___y_1609_);
v___x_1616_ = l_Lean_Expr_fvarId_x21(v_e_1608_);
v___x_1617_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1615_, v___x_1616_);
lean_dec(v___x_1616_);
v___x_1618_ = lean_st_ref_put(v___y_1609_, v___x_1617_);
v___x_1619_ = lean_box(0);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_e_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v_e_1621_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
if (lean_obj_tag(v_x_1630_) == 0)
{
return v_x_1629_;
}
else
{
lean_object* v_key_1631_; lean_object* v_value_1632_; lean_object* v_tail_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1656_; 
v_key_1631_ = lean_ctor_get(v_x_1630_, 0);
v_value_1632_ = lean_ctor_get(v_x_1630_, 1);
v_tail_1633_ = lean_ctor_get(v_x_1630_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1630_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1635_ = v_x_1630_;
v_isShared_1636_ = v_isSharedCheck_1656_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_tail_1633_);
lean_inc(v_value_1632_);
lean_inc(v_key_1631_);
lean_dec(v_x_1630_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1656_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; uint64_t v___x_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v_fold_1641_; uint64_t v___x_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; size_t v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1637_ = lean_array_get_size(v_x_1629_);
v___x_1638_ = l_Lean_instHashableFVarId_hash(v_key_1631_);
v___x_1639_ = 32ULL;
v___x_1640_ = lean_uint64_shift_right(v___x_1638_, v___x_1639_);
v_fold_1641_ = lean_uint64_xor(v___x_1638_, v___x_1640_);
v___x_1642_ = 16ULL;
v___x_1643_ = lean_uint64_shift_right(v_fold_1641_, v___x_1642_);
v___x_1644_ = lean_uint64_xor(v_fold_1641_, v___x_1643_);
v___x_1645_ = lean_uint64_to_usize(v___x_1644_);
v___x_1646_ = lean_usize_of_nat(v___x_1637_);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_sub(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_usize_land(v___x_1645_, v___x_1648_);
v___x_1650_ = lean_array_uget_borrowed(v_x_1629_, v___x_1649_);
lean_inc(v___x_1650_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 2, v___x_1650_);
v___x_1652_ = v___x_1635_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_key_1631_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_value_1632_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_array_uset(v_x_1629_, v___x_1649_, v___x_1652_);
v_x_1629_ = v___x_1653_;
v_x_1630_ = v_tail_1633_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1657_, lean_object* v_source_1658_, lean_object* v_target_1659_){
_start:
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = lean_array_get_size(v_source_1658_);
v___x_1661_ = lean_nat_dec_lt(v_i_1657_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_dec_ref(v_source_1658_);
lean_dec(v_i_1657_);
return v_target_1659_;
}
else
{
lean_object* v_es_1662_; lean_object* v___x_1663_; lean_object* v_source_1664_; lean_object* v_target_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_es_1662_ = lean_array_fget(v_source_1658_, v_i_1657_);
v___x_1663_ = lean_box(0);
v_source_1664_ = lean_array_fset(v_source_1658_, v_i_1657_, v___x_1663_);
v_target_1665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1659_, v_es_1662_);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v_i_1657_, v___x_1666_);
lean_dec(v_i_1657_);
v_i_1657_ = v___x_1667_;
v_source_1658_ = v_source_1664_;
v_target_1659_ = v_target_1665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_nbuckets_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1670_ = lean_array_get_size(v_data_1669_);
v___x_1671_ = lean_unsigned_to_nat(2u);
v_nbuckets_1672_ = lean_nat_mul(v___x_1670_, v___x_1671_);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_mk_array(v_nbuckets_1672_, v___x_1674_);
v___x_1676_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1673_, v_data_1669_, v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1677_, lean_object* v_a_1678_, lean_object* v_b_1679_){
_start:
{
lean_object* v_size_1680_; lean_object* v_buckets_1681_; lean_object* v___x_1682_; uint64_t v___x_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v_fold_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; lean_object* v_bkt_1695_; uint8_t v___x_1696_; 
v_size_1680_ = lean_ctor_get(v_m_1677_, 0);
v_buckets_1681_ = lean_ctor_get(v_m_1677_, 1);
v___x_1682_ = lean_array_get_size(v_buckets_1681_);
v___x_1683_ = l_Lean_instHashableFVarId_hash(v_a_1678_);
v___x_1684_ = 32ULL;
v___x_1685_ = lean_uint64_shift_right(v___x_1683_, v___x_1684_);
v_fold_1686_ = lean_uint64_xor(v___x_1683_, v___x_1685_);
v___x_1687_ = 16ULL;
v___x_1688_ = lean_uint64_shift_right(v_fold_1686_, v___x_1687_);
v___x_1689_ = lean_uint64_xor(v_fold_1686_, v___x_1688_);
v___x_1690_ = lean_uint64_to_usize(v___x_1689_);
v___x_1691_ = lean_usize_of_nat(v___x_1682_);
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_sub(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_usize_land(v___x_1690_, v___x_1693_);
v_bkt_1695_ = lean_array_uget_borrowed(v_buckets_1681_, v___x_1694_);
v___x_1696_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1678_, v_bkt_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1717_; 
lean_inc_ref(v_buckets_1681_);
lean_inc(v_size_1680_);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_m_1677_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; lean_object* v_unused_1719_; 
v_unused_1718_ = lean_ctor_get(v_m_1677_, 1);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v_m_1677_, 0);
lean_dec(v_unused_1719_);
v___x_1698_ = v_m_1677_;
v_isShared_1699_ = v_isSharedCheck_1717_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v_m_1677_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1717_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v_size_x27_1701_; lean_object* v___x_1702_; lean_object* v_buckets_x27_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1700_ = lean_unsigned_to_nat(1u);
v_size_x27_1701_ = lean_nat_add(v_size_1680_, v___x_1700_);
lean_dec(v_size_1680_);
lean_inc(v_bkt_1695_);
v___x_1702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1702_, 0, v_a_1678_);
lean_ctor_set(v___x_1702_, 1, v_b_1679_);
lean_ctor_set(v___x_1702_, 2, v_bkt_1695_);
v_buckets_x27_1703_ = lean_array_uset(v_buckets_1681_, v___x_1694_, v___x_1702_);
v___x_1704_ = lean_unsigned_to_nat(4u);
v___x_1705_ = lean_nat_mul(v_size_x27_1701_, v___x_1704_);
v___x_1706_ = lean_unsigned_to_nat(3u);
v___x_1707_ = lean_nat_div(v___x_1705_, v___x_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_array_get_size(v_buckets_x27_1703_);
v___x_1709_ = lean_nat_dec_le(v___x_1707_, v___x_1708_);
lean_dec(v___x_1707_);
if (v___x_1709_ == 0)
{
lean_object* v_val_1710_; lean_object* v___x_1712_; 
v_val_1710_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1703_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v_val_1710_);
lean_ctor_set(v___x_1698_, 0, v_size_x27_1701_);
v___x_1712_ = v___x_1698_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_size_x27_1701_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_val_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
else
{
lean_object* v___x_1715_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v_buckets_x27_1703_);
lean_ctor_set(v___x_1698_, 0, v_size_x27_1701_);
v___x_1715_ = v___x_1698_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_size_x27_1701_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_buckets_x27_1703_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_dec(v_b_1679_);
lean_dec(v_a_1678_);
return v_m_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1722_, size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_b_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_b_1725_);
return v___x_1732_;
}
else
{
lean_object* v_snd_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1800_; 
v_snd_1733_ = lean_ctor_get(v_b_1725_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_b_1725_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_b_1725_, 0);
lean_dec(v_unused_1801_);
v___x_1735_ = v_b_1725_;
v_isShared_1736_ = v_isSharedCheck_1800_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_snd_1733_);
lean_dec(v_b_1725_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1800_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v_a_1739_; lean_object* v_a_1746_; 
v___x_1737_ = lean_box(0);
v_a_1746_ = lean_array_uget_borrowed(v_as_1722_, v_i_1724_);
if (lean_obj_tag(v_a_1746_) == 0)
{
v_a_1739_ = v_snd_1733_;
goto v___jp_1738_;
}
else
{
lean_object* v_val_1747_; lean_object* v___y_1749_; lean_object* v___y_1754_; uint8_t v___y_1755_; uint8_t v___x_1756_; 
v_val_1747_ = lean_ctor_get(v_a_1746_, 0);
v___x_1756_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1747_);
if (v___x_1756_ == 0)
{
lean_object* v___f_1757_; lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v_candidates_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___x_1778_; 
v___f_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1759_ = l_Lean_LocalDecl_type(v_val_1747_);
lean_inc_ref(v___x_1759_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1757_, v___f_1758_, v___x_1756_, v___x_1759_, v_snd_1733_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l_Lean_LocalDecl_value_x3f(v_val_1747_, v___x_1756_);
if (lean_obj_tag(v___x_1780_) == 0)
{
v_candidates_1761_ = v_a_1779_;
v___y_1762_ = v___y_1726_;
v___y_1763_ = v___y_1727_;
v___y_1764_ = v___y_1728_;
v___y_1765_ = v___y_1729_;
goto v___jp_1760_;
}
else
{
lean_object* v_val_1781_; lean_object* v___x_1782_; 
v_val_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1757_, v___f_1758_, v___x_1756_, v_val_1781_, v_a_1779_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v_candidates_1761_ = v_a_1783_;
v___y_1762_ = v___y_1726_;
v___y_1763_ = v___y_1727_;
v___y_1764_ = v___y_1728_;
v___y_1765_ = v___y_1729_;
goto v___jp_1760_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v___x_1759_);
lean_del_object(v___x_1735_);
v_a_1784_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1782_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref(v___x_1759_);
lean_del_object(v___x_1735_);
v_a_1792_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1778_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1778_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
v___jp_1760_:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Meta_isProp(v___x_1759_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; uint8_t v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_unbox(v_a_1767_);
lean_dec(v_a_1767_);
if (v___x_1768_ == 0)
{
v___y_1754_ = v_candidates_1761_;
v___y_1755_ = v___x_1756_;
goto v___jp_1753_;
}
else
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_LocalDecl_hasValue(v_val_1747_, v___x_1756_);
if (v___x_1769_ == 0)
{
v___y_1749_ = v_candidates_1761_;
goto v___jp_1748_;
}
else
{
v___y_1754_ = v_candidates_1761_;
v___y_1755_ = v___x_1756_;
goto v___jp_1753_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_candidates_1761_);
lean_del_object(v___x_1735_);
v_a_1770_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1766_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
v_a_1739_ = v_snd_1733_;
goto v___jp_1738_;
}
v___jp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = l_Lean_LocalDecl_fvarId(v_val_1747_);
v___x_1751_ = lean_box(0);
v___x_1752_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1749_, v___x_1750_, v___x_1751_);
v_a_1739_ = v___x_1752_;
goto v___jp_1738_;
}
v___jp_1753_:
{
if (v___y_1755_ == 0)
{
v_a_1739_ = v___y_1754_;
goto v___jp_1738_;
}
else
{
v___y_1749_ = v___y_1754_;
goto v___jp_1748_;
}
}
}
v___jp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v_a_1739_);
lean_ctor_set(v___x_1735_, 0, v___x_1737_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1739_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
size_t v___x_1742_; size_t v___x_1743_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1724_, v___x_1742_);
v_i_1724_ = v___x_1743_;
v_b_1725_ = v___x_1741_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1802_, lean_object* v_sz_1803_, lean_object* v_i_1804_, lean_object* v_b_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1803_);
lean_dec(v_sz_1803_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1802_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_as_1802_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1814_, size_t v_sz_1815_, size_t v_i_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1817_);
return v___x_1824_;
}
else
{
lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1892_; 
v_snd_1825_ = lean_ctor_get(v_b_1817_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_b_1817_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v_b_1817_, 0);
lean_dec(v_unused_1893_);
v___x_1827_ = v_b_1817_;
v_isShared_1828_ = v_isSharedCheck_1892_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_dec(v_b_1817_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1892_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v_a_1831_; lean_object* v_a_1838_; 
v___x_1829_ = lean_box(0);
v_a_1838_ = lean_array_uget_borrowed(v_as_1814_, v_i_1816_);
if (lean_obj_tag(v_a_1838_) == 0)
{
v_a_1831_ = v_snd_1825_;
goto v___jp_1830_;
}
else
{
lean_object* v_val_1839_; lean_object* v___y_1841_; lean_object* v___y_1846_; uint8_t v___y_1847_; uint8_t v___x_1848_; 
v_val_1839_ = lean_ctor_get(v_a_1838_, 0);
v___x_1848_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1839_);
if (v___x_1848_ == 0)
{
lean_object* v___f_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v_candidates_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___x_1870_; 
v___f_1849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1851_ = l_Lean_LocalDecl_type(v_val_1839_);
lean_inc_ref(v___x_1851_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1849_, v___f_1850_, v___x_1848_, v___x_1851_, v_snd_1825_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l_Lean_LocalDecl_value_x3f(v_val_1839_, v___x_1848_);
if (lean_obj_tag(v___x_1872_) == 0)
{
v_candidates_1853_ = v_a_1871_;
v___y_1854_ = v___y_1818_;
v___y_1855_ = v___y_1819_;
v___y_1856_ = v___y_1820_;
v___y_1857_ = v___y_1821_;
goto v___jp_1852_;
}
else
{
lean_object* v_val_1873_; lean_object* v___x_1874_; 
v_val_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_val_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1849_, v___f_1850_, v___x_1848_, v_val_1873_, v_a_1871_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v_candidates_1853_ = v_a_1875_;
v___y_1854_ = v___y_1818_;
v___y_1855_ = v___y_1819_;
v___y_1856_ = v___y_1820_;
v___y_1857_ = v___y_1821_;
goto v___jp_1852_;
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v___x_1851_);
lean_del_object(v___x_1827_);
v_a_1876_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1874_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v___x_1851_);
lean_del_object(v___x_1827_);
v_a_1884_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1870_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1870_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
v___jp_1852_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Meta_isProp(v___x_1851_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; uint8_t v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v___x_1860_ = lean_unbox(v_a_1859_);
lean_dec(v_a_1859_);
if (v___x_1860_ == 0)
{
v___y_1846_ = v_candidates_1853_;
v___y_1847_ = v___x_1848_;
goto v___jp_1845_;
}
else
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Lean_LocalDecl_hasValue(v_val_1839_, v___x_1848_);
if (v___x_1861_ == 0)
{
v___y_1841_ = v_candidates_1853_;
goto v___jp_1840_;
}
else
{
v___y_1846_ = v_candidates_1853_;
v___y_1847_ = v___x_1848_;
goto v___jp_1845_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_candidates_1853_);
lean_del_object(v___x_1827_);
v_a_1862_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1858_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1858_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
else
{
v_a_1831_ = v_snd_1825_;
goto v___jp_1830_;
}
v___jp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_LocalDecl_fvarId(v_val_1839_);
v___x_1843_ = lean_box(0);
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1841_, v___x_1842_, v___x_1843_);
v_a_1831_ = v___x_1844_;
goto v___jp_1830_;
}
v___jp_1845_:
{
if (v___y_1847_ == 0)
{
v_a_1831_ = v___y_1846_;
goto v___jp_1830_;
}
else
{
v___y_1841_ = v___y_1846_;
goto v___jp_1840_;
}
}
}
v___jp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v_a_1831_);
lean_ctor_set(v___x_1827_, 0, v___x_1829_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1831_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_i_1816_, v___x_1834_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1814_, v_sz_1815_, v___x_1835_, v___x_1833_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1894_, lean_object* v_sz_1895_, lean_object* v_i_1896_, lean_object* v_b_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
size_t v_sz_boxed_1903_; size_t v_i_boxed_1904_; lean_object* v_res_1905_; 
v_sz_boxed_1903_ = lean_unbox_usize(v_sz_1895_);
lean_dec(v_sz_1895_);
v_i_boxed_1904_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1894_, v_sz_boxed_1903_, v_i_boxed_1904_, v_b_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v_as_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1906_, size_t v_sz_1907_, size_t v_i_1908_, lean_object* v_b_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_lt(v_i_1908_, v_sz_1907_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1909_);
return v___x_1916_;
}
else
{
lean_object* v_snd_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1984_; 
v_snd_1917_ = lean_ctor_get(v_b_1909_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_b_1909_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v_b_1909_, 0);
lean_dec(v_unused_1985_);
v___x_1919_ = v_b_1909_;
v_isShared_1920_ = v_isSharedCheck_1984_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snd_1917_);
lean_dec(v_b_1909_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1984_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v_a_1923_; lean_object* v_a_1930_; 
v___x_1921_ = lean_box(0);
v_a_1930_ = lean_array_uget_borrowed(v_as_1906_, v_i_1908_);
if (lean_obj_tag(v_a_1930_) == 0)
{
v_a_1923_ = v_snd_1917_;
goto v___jp_1922_;
}
else
{
lean_object* v_val_1931_; lean_object* v___y_1933_; lean_object* v___y_1938_; uint8_t v___y_1939_; uint8_t v___x_1940_; 
v_val_1931_ = lean_ctor_get(v_a_1930_, 0);
v___x_1940_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1931_);
if (v___x_1940_ == 0)
{
lean_object* v___f_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v_candidates_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___x_1962_; 
v___f_1941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1943_ = l_Lean_LocalDecl_type(v_val_1931_);
lean_inc_ref(v___x_1943_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1941_, v___f_1942_, v___x_1940_, v___x_1943_, v_snd_1917_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = l_Lean_LocalDecl_value_x3f(v_val_1931_, v___x_1940_);
if (lean_obj_tag(v___x_1964_) == 0)
{
v_candidates_1945_ = v_a_1963_;
v___y_1946_ = v___y_1910_;
v___y_1947_ = v___y_1911_;
v___y_1948_ = v___y_1912_;
v___y_1949_ = v___y_1913_;
goto v___jp_1944_;
}
else
{
lean_object* v_val_1965_; lean_object* v___x_1966_; 
v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1941_, v___f_1942_, v___x_1940_, v_val_1965_, v_a_1963_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v_candidates_1945_ = v_a_1967_;
v___y_1946_ = v___y_1910_;
v___y_1947_ = v___y_1911_;
v___y_1948_ = v___y_1912_;
v___y_1949_ = v___y_1913_;
goto v___jp_1944_;
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v___x_1943_);
lean_del_object(v___x_1919_);
v_a_1968_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1966_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1966_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v___x_1943_);
lean_del_object(v___x_1919_);
v_a_1976_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1962_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1962_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
v___jp_1944_:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Meta_isProp(v___x_1943_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; uint8_t v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = lean_unbox(v_a_1951_);
lean_dec(v_a_1951_);
if (v___x_1952_ == 0)
{
v___y_1938_ = v_candidates_1945_;
v___y_1939_ = v___x_1940_;
goto v___jp_1937_;
}
else
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Lean_LocalDecl_hasValue(v_val_1931_, v___x_1940_);
if (v___x_1953_ == 0)
{
v___y_1933_ = v_candidates_1945_;
goto v___jp_1932_;
}
else
{
v___y_1938_ = v_candidates_1945_;
v___y_1939_ = v___x_1940_;
goto v___jp_1937_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_candidates_1945_);
lean_del_object(v___x_1919_);
v_a_1954_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1950_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1950_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
else
{
v_a_1923_ = v_snd_1917_;
goto v___jp_1922_;
}
v___jp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = l_Lean_LocalDecl_fvarId(v_val_1931_);
v___x_1935_ = lean_box(0);
v___x_1936_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1933_, v___x_1934_, v___x_1935_);
v_a_1923_ = v___x_1936_;
goto v___jp_1922_;
}
v___jp_1937_:
{
if (v___y_1939_ == 0)
{
v_a_1923_ = v___y_1938_;
goto v___jp_1922_;
}
else
{
v___y_1933_ = v___y_1938_;
goto v___jp_1932_;
}
}
}
v___jp_1922_:
{
lean_object* v___x_1925_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v_a_1923_);
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1925_ = v___x_1919_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_a_1923_);
v___x_1925_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
size_t v___x_1926_; size_t v___x_1927_; 
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1908_, v___x_1926_);
v_i_1908_ = v___x_1927_;
v_b_1909_ = v___x_1925_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1986_, lean_object* v_sz_1987_, lean_object* v_i_1988_, lean_object* v_b_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
size_t v_sz_boxed_1995_; size_t v_i_boxed_1996_; lean_object* v_res_1997_; 
v_sz_boxed_1995_ = lean_unbox_usize(v_sz_1987_);
lean_dec(v_sz_1987_);
v_i_boxed_1996_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_res_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1986_, v_sz_boxed_1995_, v_i_boxed_1996_, v_b_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v_as_1986_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1998_, size_t v_sz_1999_, size_t v_i_2000_, lean_object* v_b_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_2000_, v_sz_1999_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_2001_);
return v___x_2008_;
}
else
{
lean_object* v_snd_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2076_; 
v_snd_2009_ = lean_ctor_get(v_b_2001_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_b_2001_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_b_2001_, 0);
lean_dec(v_unused_2077_);
v___x_2011_ = v_b_2001_;
v_isShared_2012_ = v_isSharedCheck_2076_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2009_);
lean_dec(v_b_2001_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2076_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v_a_2015_; lean_object* v_a_2022_; 
v___x_2013_ = lean_box(0);
v_a_2022_ = lean_array_uget_borrowed(v_as_1998_, v_i_2000_);
if (lean_obj_tag(v_a_2022_) == 0)
{
v_a_2015_ = v_snd_2009_;
goto v___jp_2014_;
}
else
{
lean_object* v_val_2023_; lean_object* v___y_2025_; lean_object* v___y_2030_; uint8_t v___y_2031_; uint8_t v___x_2032_; 
v_val_2023_ = lean_ctor_get(v_a_2022_, 0);
v___x_2032_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2023_);
if (v___x_2032_ == 0)
{
lean_object* v___f_2033_; lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v_candidates_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___x_2054_; 
v___f_2033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2035_ = l_Lean_LocalDecl_type(v_val_2023_);
lean_inc_ref(v___x_2035_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2033_, v___f_2034_, v___x_2032_, v___x_2035_, v_snd_2009_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = l_Lean_LocalDecl_value_x3f(v_val_2023_, v___x_2032_);
if (lean_obj_tag(v___x_2056_) == 0)
{
v_candidates_2037_ = v_a_2055_;
v___y_2038_ = v___y_2002_;
v___y_2039_ = v___y_2003_;
v___y_2040_ = v___y_2004_;
v___y_2041_ = v___y_2005_;
goto v___jp_2036_;
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2058_; 
v_val_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_val_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2033_, v___f_2034_, v___x_2032_, v_val_2057_, v_a_2055_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v_candidates_2037_ = v_a_2059_;
v___y_2038_ = v___y_2002_;
v___y_2039_ = v___y_2003_;
v___y_2040_ = v___y_2004_;
v___y_2041_ = v___y_2005_;
goto v___jp_2036_;
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v___x_2035_);
lean_del_object(v___x_2011_);
v_a_2060_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2058_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2058_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v___x_2035_);
lean_del_object(v___x_2011_);
v_a_2068_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2054_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2054_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
v___jp_2036_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Meta_isProp(v___x_2035_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; uint8_t v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = lean_unbox(v_a_2043_);
lean_dec(v_a_2043_);
if (v___x_2044_ == 0)
{
v___y_2030_ = v_candidates_2037_;
v___y_2031_ = v___x_2032_;
goto v___jp_2029_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_LocalDecl_hasValue(v_val_2023_, v___x_2032_);
if (v___x_2045_ == 0)
{
v___y_2025_ = v_candidates_2037_;
goto v___jp_2024_;
}
else
{
v___y_2030_ = v_candidates_2037_;
v___y_2031_ = v___x_2032_;
goto v___jp_2029_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec_ref(v_candidates_2037_);
lean_del_object(v___x_2011_);
v_a_2046_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2042_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2042_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
else
{
v_a_2015_ = v_snd_2009_;
goto v___jp_2014_;
}
v___jp_2024_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = l_Lean_LocalDecl_fvarId(v_val_2023_);
v___x_2027_ = lean_box(0);
v___x_2028_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2025_, v___x_2026_, v___x_2027_);
v_a_2015_ = v___x_2028_;
goto v___jp_2014_;
}
v___jp_2029_:
{
if (v___y_2031_ == 0)
{
v_a_2015_ = v___y_2030_;
goto v___jp_2014_;
}
else
{
v___y_2025_ = v___y_2030_;
goto v___jp_2024_;
}
}
}
v___jp_2014_:
{
lean_object* v___x_2017_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v_a_2015_);
lean_ctor_set(v___x_2011_, 0, v___x_2013_);
v___x_2017_ = v___x_2011_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_a_2015_);
v___x_2017_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_add(v_i_2000_, v___x_2018_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1998_, v_sz_1999_, v___x_2019_, v___x_2017_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
return v___x_2020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2078_, lean_object* v_sz_2079_, lean_object* v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
size_t v_sz_boxed_2087_; size_t v_i_boxed_2088_; lean_object* v_res_2089_; 
v_sz_boxed_2087_ = lean_unbox_usize(v_sz_2079_);
lean_dec(v_sz_2079_);
v_i_boxed_2088_ = lean_unbox_usize(v_i_2080_);
lean_dec(v_i_2080_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2078_, v_sz_boxed_2087_, v_i_boxed_2088_, v_b_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_as_2078_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2090_, lean_object* v_n_2091_, lean_object* v_b_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
if (lean_obj_tag(v_n_2091_) == 0)
{
lean_object* v_cs_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; size_t v_sz_2101_; size_t v___x_2102_; lean_object* v___x_2103_; 
v_cs_2098_ = lean_ctor_get(v_n_2091_, 0);
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_b_2092_);
v_sz_2101_ = lean_array_size(v_cs_2098_);
v___x_2102_ = ((size_t)0ULL);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2090_, v_cs_2098_, v_sz_2101_, v___x_2102_, v___x_2100_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2118_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2118_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2118_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_fst_2108_; 
v_fst_2108_ = lean_ctor_get(v_a_2104_, 0);
if (lean_obj_tag(v_fst_2108_) == 0)
{
lean_object* v_snd_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v_snd_2109_ = lean_ctor_get(v_a_2104_, 1);
lean_inc(v_snd_2109_);
lean_dec(v_a_2104_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_snd_2109_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2110_);
v___x_2112_ = v___x_2106_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
else
{
lean_object* v_val_2114_; lean_object* v___x_2116_; 
lean_inc_ref(v_fst_2108_);
lean_dec(v_a_2104_);
v_val_2114_ = lean_ctor_get(v_fst_2108_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v_fst_2108_, 1);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v_val_2114_);
v___x_2116_ = v___x_2106_;
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
v_a_2119_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2103_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2103_);
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
lean_object* v_vs_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v_vs_2127_ = lean_ctor_get(v_n_2091_, 0);
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v_b_2092_);
v_sz_2130_ = lean_array_size(v_vs_2127_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2127_, v_sz_2130_, v___x_2131_, v___x_2129_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_fst_2137_; 
v_fst_2137_ = lean_ctor_get(v_a_2133_, 0);
if (lean_obj_tag(v_fst_2137_) == 0)
{
lean_object* v_snd_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v_snd_2138_ = lean_ctor_get(v_a_2133_, 1);
lean_inc(v_snd_2138_);
lean_dec(v_a_2133_);
v___x_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_snd_2138_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2139_);
v___x_2141_ = v___x_2135_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
lean_object* v_val_2143_; lean_object* v___x_2145_; 
lean_inc_ref(v_fst_2137_);
lean_dec(v_a_2133_);
v_val_2143_ = lean_ctor_get(v_fst_2137_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_fst_2137_, 1);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v_val_2143_);
v___x_2145_ = v___x_2135_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_val_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_a_2148_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2132_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2132_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2156_, lean_object* v_as_2157_, size_t v_sz_2158_, size_t v_i_2159_, lean_object* v_b_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_lt(v_i_2159_, v_sz_2158_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_b_2160_);
return v___x_2167_;
}
else
{
lean_object* v_snd_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2202_; 
v_snd_2168_ = lean_ctor_get(v_b_2160_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_b_2160_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v_b_2160_, 0);
lean_dec(v_unused_2203_);
v___x_2170_ = v_b_2160_;
v_isShared_2171_ = v_isSharedCheck_2202_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_snd_2168_);
lean_dec(v_b_2160_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2202_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_array_uget_borrowed(v_as_2157_, v_i_2159_);
lean_inc(v_snd_2168_);
v___x_2173_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2156_, v_a_2172_, v_snd_2168_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2193_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2193_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2193_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
if (lean_obj_tag(v_a_2174_) == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_a_2174_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2178_);
v___x_2180_ = v___x_2170_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_snd_2168_);
v___x_2180_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2182_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2180_);
v___x_2182_ = v___x_2176_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
lean_del_object(v___x_2176_);
lean_dec(v_snd_2168_);
v_a_2185_ = lean_ctor_get(v_a_2174_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v_a_2174_, 1);
v___x_2186_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v_a_2185_);
lean_ctor_set(v___x_2170_, 0, v___x_2186_);
v___x_2188_ = v___x_2170_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_a_2185_);
v___x_2188_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
size_t v___x_2189_; size_t v___x_2190_; 
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2159_, v___x_2189_);
v_i_2159_ = v___x_2190_;
v_b_2160_ = v___x_2188_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_del_object(v___x_2170_);
lean_dec(v_snd_2168_);
v_a_2194_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2173_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2173_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2204_, lean_object* v_as_2205_, lean_object* v_sz_2206_, lean_object* v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
size_t v_sz_boxed_2214_; size_t v_i_boxed_2215_; lean_object* v_res_2216_; 
v_sz_boxed_2214_ = lean_unbox_usize(v_sz_2206_);
lean_dec(v_sz_2206_);
v_i_boxed_2215_ = lean_unbox_usize(v_i_2207_);
lean_dec(v_i_2207_);
v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2204_, v_as_2205_, v_sz_boxed_2214_, v_i_boxed_2215_, v_b_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_as_2205_);
lean_dec_ref(v_init_2204_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2217_, lean_object* v_n_2218_, lean_object* v_b_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2217_, v_n_2218_, v_b_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec_ref(v_n_2218_);
lean_dec_ref(v_init_2217_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2226_, lean_object* v_init_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_root_2233_; lean_object* v_tail_2234_; lean_object* v___x_2235_; 
v_root_2233_ = lean_ctor_get(v_t_2226_, 0);
v_tail_2234_ = lean_ctor_get(v_t_2226_, 1);
lean_inc_ref(v_init_2227_);
v___x_2235_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2227_, v_root_2233_, v_init_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec_ref(v_init_2227_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2272_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2272_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2272_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; 
v_a_2240_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v_a_2236_, 1);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_a_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
lean_del_object(v___x_2238_);
v_a_2244_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v_a_2236_, 1);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v_a_2244_);
v_sz_2247_ = lean_array_size(v_tail_2234_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2234_, v_sz_2247_, v___x_2248_, v___x_2246_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2263_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2263_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_fst_2254_; 
v_fst_2254_ = lean_ctor_get(v_a_2250_, 0);
if (lean_obj_tag(v_fst_2254_) == 0)
{
lean_object* v_snd_2255_; lean_object* v___x_2257_; 
v_snd_2255_ = lean_ctor_get(v_a_2250_, 1);
lean_inc(v_snd_2255_);
lean_dec(v_a_2250_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_snd_2255_);
v___x_2257_ = v___x_2252_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_snd_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
else
{
lean_object* v_val_2259_; lean_object* v___x_2261_; 
lean_inc_ref(v_fst_2254_);
lean_dec(v_a_2250_);
v_val_2259_ = lean_ctor_get(v_fst_2254_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v_fst_2254_, 1);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_val_2259_);
v___x_2261_ = v___x_2252_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_val_2259_);
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
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2235_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2235_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2281_, lean_object* v_init_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2281_, v_init_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec_ref(v_t_2281_);
return v_res_2288_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_buckets_2291_; lean_object* v___x_2292_; uint64_t v___x_2293_; uint64_t v___x_2294_; uint64_t v___x_2295_; uint64_t v_fold_2296_; uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_buckets_2291_ = lean_ctor_get(v_m_2289_, 1);
v___x_2292_ = lean_array_get_size(v_buckets_2291_);
v___x_2293_ = l_Lean_instHashableFVarId_hash(v_a_2290_);
v___x_2294_ = 32ULL;
v___x_2295_ = lean_uint64_shift_right(v___x_2293_, v___x_2294_);
v_fold_2296_ = lean_uint64_xor(v___x_2293_, v___x_2295_);
v___x_2297_ = 16ULL;
v___x_2298_ = lean_uint64_shift_right(v_fold_2296_, v___x_2297_);
v___x_2299_ = lean_uint64_xor(v_fold_2296_, v___x_2298_);
v___x_2300_ = lean_uint64_to_usize(v___x_2299_);
v___x_2301_ = lean_usize_of_nat(v___x_2292_);
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_sub(v___x_2301_, v___x_2302_);
v___x_2304_ = lean_usize_land(v___x_2300_, v___x_2303_);
v___x_2305_ = lean_array_uget_borrowed(v_buckets_2291_, v___x_2304_);
v___x_2306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2290_, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2307_, lean_object* v_a_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec_ref(v_m_2307_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2311_, lean_object* v_as_2312_, size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_b_2315_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_b_2315_);
return v___x_2318_;
}
else
{
lean_object* v_snd_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2337_; 
v_snd_2319_ = lean_ctor_get(v_b_2315_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_b_2315_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v_b_2315_, 0);
lean_dec(v_unused_2338_);
v___x_2321_ = v_b_2315_;
v_isShared_2322_ = v_isSharedCheck_2337_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_snd_2319_);
lean_dec(v_b_2315_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2337_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v_a_2325_; lean_object* v_a_2332_; 
v___x_2323_ = lean_box(0);
v_a_2332_ = lean_array_uget_borrowed(v_as_2312_, v_i_2314_);
if (lean_obj_tag(v_a_2332_) == 0)
{
v_a_2325_ = v_snd_2319_;
goto v___jp_2324_;
}
else
{
lean_object* v_val_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_val_2333_ = lean_ctor_get(v_a_2332_, 0);
v___x_2334_ = l_Lean_LocalDecl_fvarId(v_val_2333_);
v___x_2335_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2311_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_dec(v___x_2334_);
v_a_2325_ = v_snd_2319_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_array_push(v_snd_2319_, v___x_2334_);
v_a_2325_ = v___x_2336_;
goto v___jp_2324_;
}
}
v___jp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v_a_2325_);
lean_ctor_set(v___x_2321_, 0, v___x_2323_);
v___x_2327_ = v___x_2321_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_a_2325_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
size_t v___x_2328_; size_t v___x_2329_; 
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2314_, v___x_2328_);
v_i_2314_ = v___x_2329_;
v_b_2315_ = v___x_2327_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2339_, lean_object* v_as_2340_, lean_object* v_sz_2341_, lean_object* v_i_2342_, lean_object* v_b_2343_, lean_object* v___y_2344_){
_start:
{
size_t v_sz_boxed_2345_; size_t v_i_boxed_2346_; lean_object* v_res_2347_; 
v_sz_boxed_2345_ = lean_unbox_usize(v_sz_2341_);
lean_dec(v_sz_2341_);
v_i_boxed_2346_ = lean_unbox_usize(v_i_2342_);
lean_dec(v_i_2342_);
v_res_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2339_, v_as_2340_, v_sz_boxed_2345_, v_i_boxed_2346_, v_b_2343_);
lean_dec_ref(v_as_2340_);
lean_dec_ref(v_a_2339_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2348_, lean_object* v_as_2349_, size_t v_sz_2350_, size_t v_i_2351_, lean_object* v_b_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_usize_dec_lt(v_i_2351_, v_sz_2350_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v_b_2352_);
return v___x_2359_;
}
else
{
lean_object* v_snd_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2378_; 
v_snd_2360_ = lean_ctor_get(v_b_2352_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_b_2352_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_b_2352_, 0);
lean_dec(v_unused_2379_);
v___x_2362_ = v_b_2352_;
v_isShared_2363_ = v_isSharedCheck_2378_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_snd_2360_);
lean_dec(v_b_2352_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2378_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v_a_2366_; lean_object* v_a_2373_; 
v___x_2364_ = lean_box(0);
v_a_2373_ = lean_array_uget_borrowed(v_as_2349_, v_i_2351_);
if (lean_obj_tag(v_a_2373_) == 0)
{
v_a_2366_ = v_snd_2360_;
goto v___jp_2365_;
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_val_2374_ = lean_ctor_get(v_a_2373_, 0);
v___x_2375_ = l_Lean_LocalDecl_fvarId(v_val_2374_);
v___x_2376_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2348_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_dec(v___x_2375_);
v_a_2366_ = v_snd_2360_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_array_push(v_snd_2360_, v___x_2375_);
v_a_2366_ = v___x_2377_;
goto v___jp_2365_;
}
}
v___jp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v_a_2366_);
lean_ctor_set(v___x_2362_, 0, v___x_2364_);
v___x_2368_ = v___x_2362_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_a_2366_);
v___x_2368_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
size_t v___x_2369_; size_t v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = ((size_t)1ULL);
v___x_2370_ = lean_usize_add(v_i_2351_, v___x_2369_);
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2348_, v_as_2349_, v_sz_2350_, v___x_2370_, v___x_2368_);
return v___x_2371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2380_, lean_object* v_as_2381_, lean_object* v_sz_2382_, lean_object* v_i_2383_, lean_object* v_b_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
size_t v_sz_boxed_2390_; size_t v_i_boxed_2391_; lean_object* v_res_2392_; 
v_sz_boxed_2390_ = lean_unbox_usize(v_sz_2382_);
lean_dec(v_sz_2382_);
v_i_boxed_2391_ = lean_unbox_usize(v_i_2383_);
lean_dec(v_i_2383_);
v_res_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2380_, v_as_2381_, v_sz_boxed_2390_, v_i_boxed_2391_, v_b_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v_as_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2393_, lean_object* v_a_2394_, lean_object* v_n_2395_, lean_object* v_b_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
if (lean_obj_tag(v_n_2395_) == 0)
{
lean_object* v_cs_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; size_t v_sz_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v_cs_2402_ = lean_ctor_get(v_n_2395_, 0);
v___x_2403_ = lean_box(0);
v___x_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_b_2396_);
v_sz_2405_ = lean_array_size(v_cs_2402_);
v___x_2406_ = ((size_t)0ULL);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2393_, v_a_2394_, v_cs_2402_, v_sz_2405_, v___x_2406_, v___x_2404_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2422_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2422_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_fst_2412_; 
v_fst_2412_ = lean_ctor_get(v_a_2408_, 0);
if (lean_obj_tag(v_fst_2412_) == 0)
{
lean_object* v_snd_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_snd_2413_ = lean_ctor_get(v_a_2408_, 1);
lean_inc(v_snd_2413_);
lean_dec(v_a_2408_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_snd_2413_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2414_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
else
{
lean_object* v_val_2418_; lean_object* v___x_2420_; 
lean_inc_ref(v_fst_2412_);
lean_dec(v_a_2408_);
v_val_2418_ = lean_ctor_get(v_fst_2412_, 0);
lean_inc(v_val_2418_);
lean_dec_ref_known(v_fst_2412_, 1);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v_val_2418_);
v___x_2420_ = v___x_2410_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_val_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
v_a_2423_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2407_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2407_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_vs_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; size_t v_sz_2434_; size_t v___x_2435_; lean_object* v___x_2436_; 
v_vs_2431_ = lean_ctor_get(v_n_2395_, 0);
v___x_2432_ = lean_box(0);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v_b_2396_);
v_sz_2434_ = lean_array_size(v_vs_2431_);
v___x_2435_ = ((size_t)0ULL);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2394_, v_vs_2431_, v_sz_2434_, v___x_2435_, v___x_2433_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2451_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2451_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2451_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v_fst_2441_; 
v_fst_2441_ = lean_ctor_get(v_a_2437_, 0);
if (lean_obj_tag(v_fst_2441_) == 0)
{
lean_object* v_snd_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v_snd_2442_ = lean_ctor_get(v_a_2437_, 1);
lean_inc(v_snd_2442_);
lean_dec(v_a_2437_);
v___x_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2443_, 0, v_snd_2442_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2443_);
v___x_2445_ = v___x_2439_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2449_; 
lean_inc_ref(v_fst_2441_);
lean_dec(v_a_2437_);
v_val_2447_ = lean_ctor_get(v_fst_2441_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v_fst_2441_, 1);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_val_2447_);
v___x_2449_ = v___x_2439_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_val_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2436_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2436_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2460_, lean_object* v_a_2461_, lean_object* v_as_2462_, size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_b_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_b_2465_);
return v___x_2472_;
}
else
{
lean_object* v_snd_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2507_; 
v_snd_2473_ = lean_ctor_get(v_b_2465_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_b_2465_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v_b_2465_, 0);
lean_dec(v_unused_2508_);
v___x_2475_ = v_b_2465_;
v_isShared_2476_ = v_isSharedCheck_2507_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_snd_2473_);
lean_dec(v_b_2465_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2507_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_a_2477_; lean_object* v___x_2478_; 
v_a_2477_ = lean_array_uget_borrowed(v_as_2462_, v_i_2464_);
lean_inc(v_snd_2473_);
v___x_2478_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2460_, v_a_2461_, v_a_2477_, v_snd_2473_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2498_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2498_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2498_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
if (lean_obj_tag(v_a_2479_) == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2479_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2483_);
v___x_2485_ = v___x_2475_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_snd_2473_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2485_);
v___x_2487_ = v___x_2481_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_del_object(v___x_2481_);
lean_dec(v_snd_2473_);
v_a_2490_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v_a_2479_, 1);
v___x_2491_ = lean_box(0);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v_a_2490_);
lean_ctor_set(v___x_2475_, 0, v___x_2491_);
v___x_2493_ = v___x_2475_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_a_2490_);
v___x_2493_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
size_t v___x_2494_; size_t v___x_2495_; 
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_add(v_i_2464_, v___x_2494_);
v_i_2464_ = v___x_2495_;
v_b_2465_ = v___x_2493_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_del_object(v___x_2475_);
lean_dec(v_snd_2473_);
v_a_2499_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2478_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2478_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2509_, lean_object* v_a_2510_, lean_object* v_as_2511_, lean_object* v_sz_2512_, lean_object* v_i_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
size_t v_sz_boxed_2520_; size_t v_i_boxed_2521_; lean_object* v_res_2522_; 
v_sz_boxed_2520_ = lean_unbox_usize(v_sz_2512_);
lean_dec(v_sz_2512_);
v_i_boxed_2521_ = lean_unbox_usize(v_i_2513_);
lean_dec(v_i_2513_);
v_res_2522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2509_, v_a_2510_, v_as_2511_, v_sz_boxed_2520_, v_i_boxed_2521_, v_b_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v_as_2511_);
lean_dec_ref(v_a_2510_);
lean_dec_ref(v_init_2509_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2523_, lean_object* v_a_2524_, lean_object* v_n_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2523_, v_a_2524_, v_n_2525_, v_b_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_n_2525_);
lean_dec_ref(v_a_2524_);
lean_dec_ref(v_init_2523_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2533_, lean_object* v_as_2534_, size_t v_sz_2535_, size_t v_i_2536_, lean_object* v_b_2537_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_lt(v_i_2536_, v_sz_2535_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_b_2537_);
return v___x_2540_;
}
else
{
lean_object* v_snd_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2559_; 
v_snd_2541_ = lean_ctor_get(v_b_2537_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_b_2537_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_b_2537_, 0);
lean_dec(v_unused_2560_);
v___x_2543_ = v_b_2537_;
v_isShared_2544_ = v_isSharedCheck_2559_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snd_2541_);
lean_dec(v_b_2537_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2559_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v_a_2547_; lean_object* v_a_2554_; 
v___x_2545_ = lean_box(0);
v_a_2554_ = lean_array_uget_borrowed(v_as_2534_, v_i_2536_);
if (lean_obj_tag(v_a_2554_) == 0)
{
v_a_2547_ = v_snd_2541_;
goto v___jp_2546_;
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_val_2555_ = lean_ctor_get(v_a_2554_, 0);
v___x_2556_ = l_Lean_LocalDecl_fvarId(v_val_2555_);
v___x_2557_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2533_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_dec(v___x_2556_);
v_a_2547_ = v_snd_2541_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_array_push(v_snd_2541_, v___x_2556_);
v_a_2547_ = v___x_2558_;
goto v___jp_2546_;
}
}
v___jp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v_a_2547_);
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2549_ = v___x_2543_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_a_2547_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
size_t v___x_2550_; size_t v___x_2551_; 
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2536_, v___x_2550_);
v_i_2536_ = v___x_2551_;
v_b_2537_ = v___x_2549_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2561_, lean_object* v_as_2562_, lean_object* v_sz_2563_, lean_object* v_i_2564_, lean_object* v_b_2565_, lean_object* v___y_2566_){
_start:
{
size_t v_sz_boxed_2567_; size_t v_i_boxed_2568_; lean_object* v_res_2569_; 
v_sz_boxed_2567_ = lean_unbox_usize(v_sz_2563_);
lean_dec(v_sz_2563_);
v_i_boxed_2568_ = lean_unbox_usize(v_i_2564_);
lean_dec(v_i_2564_);
v_res_2569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2561_, v_as_2562_, v_sz_boxed_2567_, v_i_boxed_2568_, v_b_2565_);
lean_dec_ref(v_as_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2570_, lean_object* v_as_2571_, size_t v_sz_2572_, size_t v_i_2573_, lean_object* v_b_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v___x_2580_; 
v___x_2580_ = lean_usize_dec_lt(v_i_2573_, v_sz_2572_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_b_2574_);
return v___x_2581_;
}
else
{
lean_object* v_snd_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2600_; 
v_snd_2582_ = lean_ctor_get(v_b_2574_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_b_2574_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v_b_2574_, 0);
lean_dec(v_unused_2601_);
v___x_2584_ = v_b_2574_;
v_isShared_2585_ = v_isSharedCheck_2600_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snd_2582_);
lean_dec(v_b_2574_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2600_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v_a_2588_; lean_object* v_a_2595_; 
v___x_2586_ = lean_box(0);
v_a_2595_ = lean_array_uget_borrowed(v_as_2571_, v_i_2573_);
if (lean_obj_tag(v_a_2595_) == 0)
{
v_a_2588_ = v_snd_2582_;
goto v___jp_2587_;
}
else
{
lean_object* v_val_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v_val_2596_ = lean_ctor_get(v_a_2595_, 0);
v___x_2597_ = l_Lean_LocalDecl_fvarId(v_val_2596_);
v___x_2598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2570_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_dec(v___x_2597_);
v_a_2588_ = v_snd_2582_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_array_push(v_snd_2582_, v___x_2597_);
v_a_2588_ = v___x_2599_;
goto v___jp_2587_;
}
}
v___jp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v_a_2588_);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2590_ = v___x_2584_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_a_2588_);
v___x_2590_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = ((size_t)1ULL);
v___x_2592_ = lean_usize_add(v_i_2573_, v___x_2591_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2570_, v_as_2571_, v_sz_2572_, v___x_2592_, v___x_2590_);
return v___x_2593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2602_, lean_object* v_as_2603_, lean_object* v_sz_2604_, lean_object* v_i_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
size_t v_sz_boxed_2612_; size_t v_i_boxed_2613_; lean_object* v_res_2614_; 
v_sz_boxed_2612_ = lean_unbox_usize(v_sz_2604_);
lean_dec(v_sz_2604_);
v_i_boxed_2613_ = lean_unbox_usize(v_i_2605_);
lean_dec(v_i_2605_);
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2602_, v_as_2603_, v_sz_boxed_2612_, v_i_boxed_2613_, v_b_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_as_2603_);
lean_dec_ref(v_a_2602_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2615_, lean_object* v_t_2616_, lean_object* v_init_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_root_2623_; lean_object* v_tail_2624_; lean_object* v___x_2625_; 
v_root_2623_ = lean_ctor_get(v_t_2616_, 0);
v_tail_2624_ = lean_ctor_get(v_t_2616_, 1);
lean_inc_ref(v_init_2617_);
v___x_2625_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2617_, v_a_2615_, v_root_2623_, v_init_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec_ref(v_init_2617_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2662_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2662_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2662_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
if (lean_obj_tag(v_a_2626_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; 
v_a_2630_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v_a_2626_, 1);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_a_2630_);
v___x_2632_ = v___x_2628_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; size_t v_sz_2637_; size_t v___x_2638_; lean_object* v___x_2639_; 
lean_del_object(v___x_2628_);
v_a_2634_ = lean_ctor_get(v_a_2626_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v_a_2626_, 1);
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v_a_2634_);
v_sz_2637_ = lean_array_size(v_tail_2624_);
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2615_, v_tail_2624_, v_sz_2637_, v___x_2638_, v___x_2636_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2653_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2653_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2653_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_fst_2644_; 
v_fst_2644_ = lean_ctor_get(v_a_2640_, 0);
if (lean_obj_tag(v_fst_2644_) == 0)
{
lean_object* v_snd_2645_; lean_object* v___x_2647_; 
v_snd_2645_ = lean_ctor_get(v_a_2640_, 1);
lean_inc(v_snd_2645_);
lean_dec(v_a_2640_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_snd_2645_);
v___x_2647_ = v___x_2642_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_snd_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v_val_2649_; lean_object* v___x_2651_; 
lean_inc_ref(v_fst_2644_);
lean_dec(v_a_2640_);
v_val_2649_ = lean_ctor_get(v_fst_2644_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v_fst_2644_, 1);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v_val_2649_);
v___x_2651_ = v___x_2642_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_val_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2639_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2639_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v_a_2663_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2625_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2625_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2671_, lean_object* v_t_2672_, lean_object* v_init_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2671_, v_t_2672_, v_init_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_t_2672_);
lean_dec_ref(v_a_2671_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2682_, lean_object* v_mvarId_2683_, lean_object* v___f_2684_, lean_object* v___f_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_lctx_2691_; lean_object* v_decls_2692_; lean_object* v___x_2693_; 
v_lctx_2691_ = lean_ctor_get(v___y_2686_, 2);
v_decls_2692_ = lean_ctor_get(v_lctx_2691_, 1);
lean_inc_ref(v_decls_2692_);
v___x_2693_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2692_, v_candidates_2682_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = l_Lean_MVarId_getType(v_mvarId_2683_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v___y_2701_; uint8_t v___x_2725_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2696_, v___y_2687_);
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = lean_st_mk_ref(v_a_2694_);
v___x_2725_ = l_Lean_Expr_hasFVar(v_a_2698_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_dec(v_a_2698_);
lean_dec_ref(v___f_2685_);
v___x_2726_ = lean_box(0);
lean_inc(v___y_2689_);
lean_inc_ref(v___y_2688_);
lean_inc(v___y_2687_);
lean_inc_ref(v___y_2686_);
lean_inc(v___x_2699_);
v___x_2727_ = lean_apply_7(v___f_2684_, v___x_2726_, v___x_2699_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, lean_box(0));
v___y_2701_ = v___x_2727_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2729_ = 0;
v___x_2730_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2728_, v___f_2685_, v_a_2698_, v___x_2729_, v___x_2699_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
lean_inc(v___y_2689_);
lean_inc_ref(v___y_2688_);
lean_inc(v___y_2687_);
lean_inc_ref(v___y_2686_);
lean_inc(v___x_2699_);
v___x_2732_ = lean_apply_7(v___f_2684_, v_a_2731_, v___x_2699_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, lean_box(0));
v___y_2701_ = v___x_2732_;
goto v___jp_2700_;
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v___x_2699_);
lean_dec_ref(v_decls_2692_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v___f_2684_);
v_a_2733_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2730_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2730_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
v___jp_2700_:
{
if (lean_obj_tag(v___y_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2716_; 
v_a_2702_ = lean_ctor_get(v___y_2701_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___y_2701_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2704_ = v___y_2701_;
v_isShared_2705_ = v_isSharedCheck_2716_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___y_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2716_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v_size_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2706_ = lean_st_ref_get(v___x_2699_);
lean_dec(v___x_2699_);
lean_dec(v___x_2706_);
v_size_2707_ = lean_ctor_get(v_a_2702_, 0);
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_nat_dec_eq(v_size_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_del_object(v___x_2704_);
v___x_2710_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2711_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2702_, v_decls_2692_, v___x_2710_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_decls_2692_);
lean_dec(v_a_2702_);
return v___x_2711_;
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
lean_dec(v_a_2702_);
lean_dec_ref(v_decls_2692_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
v___x_2712_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2712_);
v___x_2714_ = v___x_2704_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v___x_2699_);
lean_dec_ref(v_decls_2692_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
v_a_2717_ = lean_ctor_get(v___y_2701_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___y_2701_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___y_2701_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___y_2701_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2694_);
lean_dec_ref(v_decls_2692_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v___f_2685_);
lean_dec_ref(v___f_2684_);
v_a_2741_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2695_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2695_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v_decls_2692_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v___f_2685_);
lean_dec_ref(v___f_2684_);
lean_dec(v_mvarId_2683_);
v_a_2749_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2693_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2693_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2757_, lean_object* v_mvarId_2758_, lean_object* v___f_2759_, lean_object* v___f_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2757_, v_mvarId_2758_, v___f_2759_, v___f_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___f_2775_; lean_object* v___f_2776_; lean_object* v_candidates_2777_; lean_object* v___f_2778_; lean_object* v___x_2779_; 
v___f_2775_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2776_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2777_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2769_);
v___f_2778_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2778_, 0, v_candidates_2777_);
lean_closure_set(v___f_2778_, 1, v_mvarId_2769_);
lean_closure_set(v___f_2778_, 2, v___f_2776_);
lean_closure_set(v___f_2778_, 3, v___f_2775_);
v___x_2779_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2769_, v___f_2778_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2787_, lean_object* v_m_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2788_, v_a_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2791_, lean_object* v_m_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2791_, v_m_2792_, v_a_2793_);
lean_dec(v_a_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2795_, lean_object* v_m_2796_, lean_object* v_a_2797_, lean_object* v_b_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2796_, v_a_2797_, v_b_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2800_, lean_object* v_m_2801_, lean_object* v_a_2802_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2801_, v_a_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_m_2805_, lean_object* v_a_2806_){
_start:
{
uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_res_2807_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2804_, v_m_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_m_2805_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2809_, lean_object* v_a_2810_, lean_object* v_x_2811_){
_start:
{
uint8_t v___x_2812_; 
v___x_2812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2810_, v_x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2813_, lean_object* v_a_2814_, lean_object* v_x_2815_){
_start:
{
uint8_t v_res_2816_; lean_object* v_r_2817_; 
v_res_2816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2813_, v_a_2814_, v_x_2815_);
lean_dec(v_x_2815_);
lean_dec(v_a_2814_);
v_r_2817_ = lean_box(v_res_2816_);
return v_r_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2818_, lean_object* v_a_2819_, lean_object* v_x_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2819_, v_x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2822_, lean_object* v_a_2823_, lean_object* v_x_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2822_, v_a_2823_, v_x_2824_);
lean_dec(v_a_2823_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2826_, lean_object* v_a_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2826_, v_a_2827_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2835_, v_a_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v_a_2836_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2844_, lean_object* v_data_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2847_, lean_object* v_a_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2847_, v_a_2848_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2856_, lean_object* v_a_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2856_, v_a_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec(v_a_2857_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2865_, lean_object* v_i_2866_, lean_object* v_source_2867_, lean_object* v_target_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2866_, v_source_2867_, v_target_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2870_, lean_object* v_as_2871_, size_t v_sz_2872_, size_t v_i_2873_, lean_object* v_b_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2870_, v_as_2871_, v_sz_2872_, v_i_2873_, v_b_2874_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2881_, lean_object* v_as_2882_, lean_object* v_sz_2883_, lean_object* v_i_2884_, lean_object* v_b_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
size_t v_sz_boxed_2891_; size_t v_i_boxed_2892_; lean_object* v_res_2893_; 
v_sz_boxed_2891_ = lean_unbox_usize(v_sz_2883_);
lean_dec(v_sz_2883_);
v_i_boxed_2892_ = lean_unbox_usize(v_i_2884_);
lean_dec(v_i_2884_);
v_res_2893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2881_, v_as_2882_, v_sz_boxed_2891_, v_i_boxed_2892_, v_b_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v_as_2882_);
lean_dec_ref(v_a_2881_);
return v_res_2893_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2894_, lean_object* v_m_2895_, lean_object* v_a_2896_){
_start:
{
uint8_t v___x_2897_; 
v___x_2897_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2895_, v_a_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2898_, lean_object* v_m_2899_, lean_object* v_a_2900_){
_start:
{
uint8_t v_res_2901_; lean_object* v_r_2902_; 
v_res_2901_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2898_, v_m_2899_, v_a_2900_);
lean_dec_ref(v_a_2900_);
lean_dec_ref(v_m_2899_);
v_r_2902_ = lean_box(v_res_2901_);
return v_r_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2903_, lean_object* v_m_2904_, lean_object* v_a_2905_, lean_object* v_b_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2904_, v_a_2905_, v_b_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2908_, lean_object* v_x_2909_, lean_object* v_x_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2909_, v_x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2912_, lean_object* v_as_2913_, size_t v_sz_2914_, size_t v_i_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2912_, v_as_2913_, v_sz_2914_, v_i_2915_, v_b_2916_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2923_, lean_object* v_as_2924_, lean_object* v_sz_2925_, lean_object* v_i_2926_, lean_object* v_b_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
size_t v_sz_boxed_2933_; size_t v_i_boxed_2934_; lean_object* v_res_2935_; 
v_sz_boxed_2933_ = lean_unbox_usize(v_sz_2925_);
lean_dec(v_sz_2925_);
v_i_boxed_2934_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2923_, v_as_2924_, v_sz_boxed_2933_, v_i_boxed_2934_, v_b_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_as_2924_);
lean_dec_ref(v_a_2923_);
return v_res_2935_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2936_, lean_object* v_a_2937_, lean_object* v_x_2938_){
_start:
{
uint8_t v___x_2939_; 
v___x_2939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2937_, v_x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2940_, lean_object* v_a_2941_, lean_object* v_x_2942_){
_start:
{
uint8_t v_res_2943_; lean_object* v_r_2944_; 
v_res_2943_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2940_, v_a_2941_, v_x_2942_);
lean_dec(v_x_2942_);
lean_dec_ref(v_a_2941_);
v_r_2944_ = lean_box(v_res_2943_);
return v_r_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2945_, lean_object* v_data_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2948_, lean_object* v_i_2949_, lean_object* v_source_2950_, lean_object* v_target_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2949_, v_source_2950_, v_target_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2954_, v_x_2955_);
return v___x_2956_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = l_Lean_maxRecDepthErrorMessage;
v___x_2963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2965_ = l_Lean_MessageData_ofFormat(v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2967_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2968_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2969_){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_ref_2969_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2977_, lean_object* v_ref_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2978_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_2986_, lean_object* v_ref_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_2986_, v_ref_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_2995_, lean_object* v_mvarId_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_toCold_3003_; lean_object* v_options_3004_; lean_object* v_currRecDepth_3005_; lean_object* v_maxRecDepth_3006_; lean_object* v_ref_3007_; lean_object* v_currNamespace_3008_; lean_object* v_openDecls_3009_; lean_object* v_initHeartbeats_3010_; lean_object* v_maxHeartbeats_3011_; lean_object* v_currMacroScope_3012_; uint8_t v_diag_3013_; uint8_t v_suppressElabErrors_3014_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v_toCold_3003_ = lean_ctor_get(v_a_3000_, 0);
v_options_3004_ = lean_ctor_get(v_a_3000_, 1);
v_currRecDepth_3005_ = lean_ctor_get(v_a_3000_, 2);
v_maxRecDepth_3006_ = lean_ctor_get(v_a_3000_, 3);
v_ref_3007_ = lean_ctor_get(v_a_3000_, 4);
v_currNamespace_3008_ = lean_ctor_get(v_a_3000_, 5);
v_openDecls_3009_ = lean_ctor_get(v_a_3000_, 6);
v_initHeartbeats_3010_ = lean_ctor_get(v_a_3000_, 7);
v_maxHeartbeats_3011_ = lean_ctor_get(v_a_3000_, 8);
v_currMacroScope_3012_ = lean_ctor_get(v_a_3000_, 9);
v_diag_3013_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*10);
v_suppressElabErrors_3014_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*10 + 1);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_nat_dec_eq(v_maxRecDepth_3006_, v___x_3042_);
if (v___x_3043_ == 0)
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_nat_dec_eq(v_currRecDepth_3005_, v_maxRecDepth_3006_);
if (v___x_3044_ == 0)
{
goto v___jp_3015_;
}
else
{
lean_object* v___x_3045_; 
lean_dec(v_mvarId_2996_);
lean_dec_ref(v_x_2995_);
lean_inc(v_ref_3007_);
v___x_3045_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3007_);
return v___x_3045_;
}
}
else
{
goto v___jp_3015_;
}
v___jp_3015_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = lean_unsigned_to_nat(1u);
v___x_3017_ = lean_nat_add(v_currRecDepth_3005_, v___x_3016_);
lean_inc(v_currMacroScope_3012_);
lean_inc(v_maxHeartbeats_3011_);
lean_inc(v_initHeartbeats_3010_);
lean_inc(v_openDecls_3009_);
lean_inc(v_currNamespace_3008_);
lean_inc(v_ref_3007_);
lean_inc(v_maxRecDepth_3006_);
lean_inc_ref(v_options_3004_);
lean_inc_ref(v_toCold_3003_);
v___x_3018_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3018_, 0, v_toCold_3003_);
lean_ctor_set(v___x_3018_, 1, v_options_3004_);
lean_ctor_set(v___x_3018_, 2, v___x_3017_);
lean_ctor_set(v___x_3018_, 3, v_maxRecDepth_3006_);
lean_ctor_set(v___x_3018_, 4, v_ref_3007_);
lean_ctor_set(v___x_3018_, 5, v_currNamespace_3008_);
lean_ctor_set(v___x_3018_, 6, v_openDecls_3009_);
lean_ctor_set(v___x_3018_, 7, v_initHeartbeats_3010_);
lean_ctor_set(v___x_3018_, 8, v_maxHeartbeats_3011_);
lean_ctor_set(v___x_3018_, 9, v_currMacroScope_3012_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*10, v_diag_3013_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*10 + 1, v_suppressElabErrors_3014_);
lean_inc_ref(v_x_2995_);
lean_inc(v_a_3001_);
lean_inc_ref(v___x_3018_);
lean_inc(v_a_2999_);
lean_inc_ref(v_a_2998_);
lean_inc(v_mvarId_2996_);
v___x_3019_ = lean_apply_6(v_x_2995_, v_mvarId_2996_, v_a_2998_, v_a_2999_, v___x_3018_, v_a_3001_, lean_box(0));
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3033_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
if (lean_obj_tag(v_a_3020_) == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
lean_dec_ref_known(v___x_3018_, 10);
lean_dec_ref(v_x_2995_);
v___x_3024_ = lean_st_ref_take(v_a_2997_);
v___x_3025_ = lean_array_push(v___x_3024_, v_mvarId_2996_);
v___x_3026_ = lean_st_ref_put(v_a_2997_, v___x_3025_);
v___x_3027_ = lean_box(0);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3027_);
v___x_3029_ = v___x_3022_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
else
{
lean_object* v_val_3031_; lean_object* v___x_3032_; 
lean_del_object(v___x_3022_);
lean_dec(v_mvarId_2996_);
v_val_3031_ = lean_ctor_get(v_a_3020_, 0);
lean_inc(v_val_3031_);
lean_dec_ref_known(v_a_3020_, 1);
v___x_3032_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_2995_, v_val_3031_, v_a_2997_, v_a_2998_, v_a_2999_, v___x_3018_, v_a_3001_);
lean_dec_ref_known(v___x_3018_, 10);
return v___x_3032_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref_known(v___x_3018_, 10);
lean_dec(v_mvarId_2996_);
lean_dec_ref(v_x_2995_);
v_a_3034_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3019_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3019_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
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
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3046_, lean_object* v_as_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
if (lean_obj_tag(v_as_3047_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref(v_x_3046_);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
else
{
lean_object* v_head_3056_; lean_object* v_tail_3057_; lean_object* v___x_3058_; 
v_head_3056_ = lean_ctor_get(v_as_3047_, 0);
lean_inc(v_head_3056_);
v_tail_3057_ = lean_ctor_get(v_as_3047_, 1);
lean_inc(v_tail_3057_);
lean_dec_ref_known(v_as_3047_, 2);
lean_inc_ref(v_x_3046_);
v___x_3058_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3046_, v_head_3056_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_dec_ref_known(v___x_3058_, 1);
v_as_3047_ = v_tail_3057_;
goto _start;
}
else
{
lean_dec(v_tail_3057_);
lean_dec_ref(v_x_3046_);
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3060_, lean_object* v_as_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3060_, v_as_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3069_, lean_object* v_mvarId_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3069_, v_mvarId_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3078_, lean_object* v_x_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3086_ = lean_st_mk_ref(v___x_3085_);
v___x_3087_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3079_, v_mvarId_3078_, v___x_3086_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3096_; 
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3097_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3091_ = lean_st_ref_get(v___x_3086_);
lean_dec(v___x_3086_);
v___x_3092_ = lean_array_to_list(v___x_3091_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3092_);
v___x_3094_ = v___x_3089_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v___x_3086_);
v_a_3098_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3087_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3087_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3106_, lean_object* v_x_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Meta_saturate(v_mvarId_3106_, v_x_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3114_, lean_object* v_msg_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
if (lean_obj_tag(v_mvarIds_3114_) == 1)
{
lean_object* v_tail_3121_; 
v_tail_3121_ = lean_ctor_get(v_mvarIds_3114_, 1);
if (lean_obj_tag(v_tail_3121_) == 0)
{
lean_object* v_head_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_msg_3115_);
v_head_3122_ = lean_ctor_get(v_mvarIds_3114_, 0);
lean_inc(v_head_3122_);
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v_head_3122_);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
return v___x_3124_;
}
}
else
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3126_, lean_object* v_msg_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Meta_exactlyOne(v_mvarIds_3126_, v_msg_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_mvarIds_3126_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3134_, lean_object* v_msg_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
if (lean_obj_tag(v_mvarIds_3134_) == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec_ref(v_msg_3135_);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
else
{
lean_object* v_tail_3143_; 
v_tail_3143_ = lean_ctor_get(v_mvarIds_3134_, 1);
if (lean_obj_tag(v_tail_3143_) == 0)
{
lean_object* v_head_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec_ref(v_msg_3135_);
v_head_3144_ = lean_ctor_get(v_mvarIds_3134_, 0);
lean_inc(v_head_3144_);
v___x_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_head_3144_);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
else
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
return v___x_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3148_, lean_object* v_msg_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3148_, v_msg_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_mvarIds_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3156_, size_t v_sz_3157_, size_t v_i_3158_, lean_object* v_b_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v___x_3165_; 
v___x_3165_ = lean_usize_dec_lt(v_i_3158_, v_sz_3157_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_b_3159_);
return v___x_3166_;
}
else
{
lean_object* v_snd_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3197_; 
v_snd_3167_ = lean_ctor_get(v_b_3159_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_b_3159_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; 
v_unused_3198_ = lean_ctor_get(v_b_3159_, 0);
lean_dec(v_unused_3198_);
v___x_3169_ = v_b_3159_;
v_isShared_3170_ = v_isSharedCheck_3197_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_snd_3167_);
lean_dec(v_b_3159_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3197_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v_a_3173_; lean_object* v_a_3180_; 
v___x_3171_ = lean_box(0);
v_a_3180_ = lean_array_uget_borrowed(v_as_3156_, v_i_3158_);
if (lean_obj_tag(v_a_3180_) == 0)
{
v_a_3173_ = v_snd_3167_;
goto v___jp_3172_;
}
else
{
lean_object* v_val_3181_; uint8_t v___x_3182_; 
v_val_3181_ = lean_ctor_get(v_a_3180_, 0);
v___x_3182_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = l_Lean_LocalDecl_type(v_val_3181_);
v___x_3184_ = l_Lean_Meta_isProp(v___x_3183_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; uint8_t v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = lean_unbox(v_a_3185_);
lean_dec(v_a_3185_);
if (v___x_3186_ == 0)
{
v_a_3173_ = v_snd_3167_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = l_Lean_LocalDecl_fvarId(v_val_3181_);
v___x_3188_ = lean_array_push(v_snd_3167_, v___x_3187_);
v_a_3173_ = v___x_3188_;
goto v___jp_3172_;
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_del_object(v___x_3169_);
lean_dec(v_snd_3167_);
v_a_3189_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3184_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3184_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
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
else
{
v_a_3173_ = v_snd_3167_;
goto v___jp_3172_;
}
}
v___jp_3172_:
{
lean_object* v___x_3175_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 1, v_a_3173_);
lean_ctor_set(v___x_3169_, 0, v___x_3171_);
v___x_3175_ = v___x_3169_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_a_3173_);
v___x_3175_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
size_t v___x_3176_; size_t v___x_3177_; 
v___x_3176_ = ((size_t)1ULL);
v___x_3177_ = lean_usize_add(v_i_3158_, v___x_3176_);
v_i_3158_ = v___x_3177_;
v_b_3159_ = v___x_3175_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3199_, lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
size_t v_sz_boxed_3208_; size_t v_i_boxed_3209_; lean_object* v_res_3210_; 
v_sz_boxed_3208_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3199_, v_sz_boxed_3208_, v_i_boxed_3209_, v_b_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec_ref(v_as_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_b_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_b_3214_);
return v___x_3221_;
}
else
{
lean_object* v_snd_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3252_; 
v_snd_3222_ = lean_ctor_get(v_b_3214_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_b_3214_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v_b_3214_, 0);
lean_dec(v_unused_3253_);
v___x_3224_ = v_b_3214_;
v_isShared_3225_ = v_isSharedCheck_3252_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_snd_3222_);
lean_dec(v_b_3214_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3252_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v_a_3228_; lean_object* v_a_3235_; 
v___x_3226_ = lean_box(0);
v_a_3235_ = lean_array_uget_borrowed(v_as_3211_, v_i_3213_);
if (lean_obj_tag(v_a_3235_) == 0)
{
v_a_3228_ = v_snd_3222_;
goto v___jp_3227_;
}
else
{
lean_object* v_val_3236_; uint8_t v___x_3237_; 
v_val_3236_ = lean_ctor_get(v_a_3235_, 0);
v___x_3237_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = l_Lean_LocalDecl_type(v_val_3236_);
v___x_3239_ = l_Lean_Meta_isProp(v___x_3238_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; uint8_t v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
v___x_3241_ = lean_unbox(v_a_3240_);
lean_dec(v_a_3240_);
if (v___x_3241_ == 0)
{
v_a_3228_ = v_snd_3222_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = l_Lean_LocalDecl_fvarId(v_val_3236_);
v___x_3243_ = lean_array_push(v_snd_3222_, v___x_3242_);
v_a_3228_ = v___x_3243_;
goto v___jp_3227_;
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_del_object(v___x_3224_);
lean_dec(v_snd_3222_);
v_a_3244_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3239_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3239_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
v_a_3228_ = v_snd_3222_;
goto v___jp_3227_;
}
}
v___jp_3227_:
{
lean_object* v___x_3230_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v_a_3228_);
lean_ctor_set(v___x_3224_, 0, v___x_3226_);
v___x_3230_ = v___x_3224_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_a_3228_);
v___x_3230_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
size_t v___x_3231_; size_t v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = ((size_t)1ULL);
v___x_3232_ = lean_usize_add(v_i_3213_, v___x_3231_);
v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3211_, v_sz_3212_, v___x_3232_, v___x_3230_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3254_, lean_object* v_sz_3255_, lean_object* v_i_3256_, lean_object* v_b_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
size_t v_sz_boxed_3263_; size_t v_i_boxed_3264_; lean_object* v_res_3265_; 
v_sz_boxed_3263_ = lean_unbox_usize(v_sz_3255_);
lean_dec(v_sz_3255_);
v_i_boxed_3264_ = lean_unbox_usize(v_i_3256_);
lean_dec(v_i_3256_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3254_, v_sz_boxed_3263_, v_i_boxed_3264_, v_b_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec_ref(v_as_3254_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3266_, lean_object* v_n_3267_, lean_object* v_b_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
if (lean_obj_tag(v_n_3267_) == 0)
{
lean_object* v_cs_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; size_t v_sz_3277_; size_t v___x_3278_; lean_object* v___x_3279_; 
v_cs_3274_ = lean_ctor_get(v_n_3267_, 0);
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v_b_3268_);
v_sz_3277_ = lean_array_size(v_cs_3274_);
v___x_3278_ = ((size_t)0ULL);
v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3266_, v_cs_3274_, v_sz_3277_, v___x_3278_, v___x_3276_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3294_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3294_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3294_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v_fst_3284_; 
v_fst_3284_ = lean_ctor_get(v_a_3280_, 0);
if (lean_obj_tag(v_fst_3284_) == 0)
{
lean_object* v_snd_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v_snd_3285_ = lean_ctor_get(v_a_3280_, 1);
lean_inc(v_snd_3285_);
lean_dec(v_a_3280_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_snd_3285_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3286_);
v___x_3288_ = v___x_3282_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
else
{
lean_object* v_val_3290_; lean_object* v___x_3292_; 
lean_inc_ref(v_fst_3284_);
lean_dec(v_a_3280_);
v_val_3290_ = lean_ctor_get(v_fst_3284_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v_fst_3284_, 1);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v_val_3290_);
v___x_3292_ = v___x_3282_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_val_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_a_3295_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3279_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3279_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_vs_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; size_t v_sz_3306_; size_t v___x_3307_; lean_object* v___x_3308_; 
v_vs_3303_ = lean_ctor_get(v_n_3267_, 0);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v_b_3268_);
v_sz_3306_ = lean_array_size(v_vs_3303_);
v___x_3307_ = ((size_t)0ULL);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3303_, v_sz_3306_, v___x_3307_, v___x_3305_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3323_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3323_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3323_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_fst_3313_; 
v_fst_3313_ = lean_ctor_get(v_a_3309_, 0);
if (lean_obj_tag(v_fst_3313_) == 0)
{
lean_object* v_snd_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v_snd_3314_ = lean_ctor_get(v_a_3309_, 1);
lean_inc(v_snd_3314_);
lean_dec(v_a_3309_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v_snd_3314_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3315_);
v___x_3317_ = v___x_3311_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
else
{
lean_object* v_val_3319_; lean_object* v___x_3321_; 
lean_inc_ref(v_fst_3313_);
lean_dec(v_a_3309_);
v_val_3319_ = lean_ctor_get(v_fst_3313_, 0);
lean_inc(v_val_3319_);
lean_dec_ref_known(v_fst_3313_, 1);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v_val_3319_);
v___x_3321_ = v___x_3311_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_val_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3324_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3308_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3308_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3332_, lean_object* v_as_3333_, size_t v_sz_3334_, size_t v_i_3335_, lean_object* v_b_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_usize_dec_lt(v_i_3335_, v_sz_3334_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; 
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_b_3336_);
return v___x_3343_;
}
else
{
lean_object* v_snd_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3378_; 
v_snd_3344_ = lean_ctor_get(v_b_3336_, 1);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_b_3336_);
if (v_isSharedCheck_3378_ == 0)
{
lean_object* v_unused_3379_; 
v_unused_3379_ = lean_ctor_get(v_b_3336_, 0);
lean_dec(v_unused_3379_);
v___x_3346_ = v_b_3336_;
v_isShared_3347_ = v_isSharedCheck_3378_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_snd_3344_);
lean_dec(v_b_3336_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3378_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_array_uget_borrowed(v_as_3333_, v_i_3335_);
lean_inc(v_snd_3344_);
v___x_3349_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3332_, v_a_3348_, v_snd_3344_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3369_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3369_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3369_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
if (lean_obj_tag(v_a_3350_) == 0)
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_a_3350_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3354_);
v___x_3356_ = v___x_3346_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_snd_3344_);
v___x_3356_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3358_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3356_);
v___x_3358_ = v___x_3352_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
lean_del_object(v___x_3352_);
lean_dec(v_snd_3344_);
v_a_3361_ = lean_ctor_get(v_a_3350_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v_a_3350_, 1);
v___x_3362_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v_a_3361_);
lean_ctor_set(v___x_3346_, 0, v___x_3362_);
v___x_3364_ = v___x_3346_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_a_3361_);
v___x_3364_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
size_t v___x_3365_; size_t v___x_3366_; 
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3335_, v___x_3365_);
v_i_3335_ = v___x_3366_;
v_b_3336_ = v___x_3364_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
v_a_3370_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3349_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3349_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3380_, lean_object* v_as_3381_, lean_object* v_sz_3382_, lean_object* v_i_3383_, lean_object* v_b_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
size_t v_sz_boxed_3390_; size_t v_i_boxed_3391_; lean_object* v_res_3392_; 
v_sz_boxed_3390_ = lean_unbox_usize(v_sz_3382_);
lean_dec(v_sz_3382_);
v_i_boxed_3391_ = lean_unbox_usize(v_i_3383_);
lean_dec(v_i_3383_);
v_res_3392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3380_, v_as_3381_, v_sz_boxed_3390_, v_i_boxed_3391_, v_b_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec_ref(v_as_3381_);
lean_dec_ref(v_init_3380_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3393_, lean_object* v_n_3394_, lean_object* v_b_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3393_, v_n_3394_, v_b_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec_ref(v_n_3394_);
lean_dec_ref(v_init_3393_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3402_, size_t v_sz_3403_, size_t v_i_3404_, lean_object* v_b_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_usize_dec_lt(v_i_3404_, v_sz_3403_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v_b_3405_);
return v___x_3412_;
}
else
{
lean_object* v_snd_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3443_; 
v_snd_3413_ = lean_ctor_get(v_b_3405_, 1);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_b_3405_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; 
v_unused_3444_ = lean_ctor_get(v_b_3405_, 0);
lean_dec(v_unused_3444_);
v___x_3415_ = v_b_3405_;
v_isShared_3416_ = v_isSharedCheck_3443_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_snd_3413_);
lean_dec(v_b_3405_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3443_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v_a_3419_; lean_object* v_a_3426_; 
v___x_3417_ = lean_box(0);
v_a_3426_ = lean_array_uget_borrowed(v_as_3402_, v_i_3404_);
if (lean_obj_tag(v_a_3426_) == 0)
{
v_a_3419_ = v_snd_3413_;
goto v___jp_3418_;
}
else
{
lean_object* v_val_3427_; uint8_t v___x_3428_; 
v_val_3427_ = lean_ctor_get(v_a_3426_, 0);
v___x_3428_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = l_Lean_LocalDecl_type(v_val_3427_);
v___x_3430_ = l_Lean_Meta_isProp(v___x_3429_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; uint8_t v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = lean_unbox(v_a_3431_);
lean_dec(v_a_3431_);
if (v___x_3432_ == 0)
{
v_a_3419_ = v_snd_3413_;
goto v___jp_3418_;
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = l_Lean_LocalDecl_fvarId(v_val_3427_);
v___x_3434_ = lean_array_push(v_snd_3413_, v___x_3433_);
v_a_3419_ = v___x_3434_;
goto v___jp_3418_;
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_del_object(v___x_3415_);
lean_dec(v_snd_3413_);
v_a_3435_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3430_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3430_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
v_a_3419_ = v_snd_3413_;
goto v___jp_3418_;
}
}
v___jp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v_a_3419_);
lean_ctor_set(v___x_3415_, 0, v___x_3417_);
v___x_3421_ = v___x_3415_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_a_3419_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
size_t v___x_3422_; size_t v___x_3423_; 
v___x_3422_ = ((size_t)1ULL);
v___x_3423_ = lean_usize_add(v_i_3404_, v___x_3422_);
v_i_3404_ = v___x_3423_;
v_b_3405_ = v___x_3421_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3445_, lean_object* v_sz_3446_, lean_object* v_i_3447_, lean_object* v_b_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
size_t v_sz_boxed_3454_; size_t v_i_boxed_3455_; lean_object* v_res_3456_; 
v_sz_boxed_3454_ = lean_unbox_usize(v_sz_3446_);
lean_dec(v_sz_3446_);
v_i_boxed_3455_ = lean_unbox_usize(v_i_3447_);
lean_dec(v_i_3447_);
v_res_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3445_, v_sz_boxed_3454_, v_i_boxed_3455_, v_b_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec_ref(v_as_3445_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3457_, size_t v_sz_3458_, size_t v_i_3459_, lean_object* v_b_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_lt(v_i_3459_, v_sz_3458_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_b_3460_);
return v___x_3467_;
}
else
{
lean_object* v_snd_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3498_; 
v_snd_3468_ = lean_ctor_get(v_b_3460_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_b_3460_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v_b_3460_, 0);
lean_dec(v_unused_3499_);
v___x_3470_ = v_b_3460_;
v_isShared_3471_ = v_isSharedCheck_3498_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snd_3468_);
lean_dec(v_b_3460_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3498_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v_a_3474_; lean_object* v_a_3481_; 
v___x_3472_ = lean_box(0);
v_a_3481_ = lean_array_uget_borrowed(v_as_3457_, v_i_3459_);
if (lean_obj_tag(v_a_3481_) == 0)
{
v_a_3474_ = v_snd_3468_;
goto v___jp_3473_;
}
else
{
lean_object* v_val_3482_; uint8_t v___x_3483_; 
v_val_3482_ = lean_ctor_get(v_a_3481_, 0);
v___x_3483_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = l_Lean_LocalDecl_type(v_val_3482_);
v___x_3485_ = l_Lean_Meta_isProp(v___x_3484_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; uint8_t v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = lean_unbox(v_a_3486_);
lean_dec(v_a_3486_);
if (v___x_3487_ == 0)
{
v_a_3474_ = v_snd_3468_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = l_Lean_LocalDecl_fvarId(v_val_3482_);
v___x_3489_ = lean_array_push(v_snd_3468_, v___x_3488_);
v_a_3474_ = v___x_3489_;
goto v___jp_3473_;
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_del_object(v___x_3470_);
lean_dec(v_snd_3468_);
v_a_3490_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3485_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3485_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
v_a_3474_ = v_snd_3468_;
goto v___jp_3473_;
}
}
v___jp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v_a_3474_);
lean_ctor_set(v___x_3470_, 0, v___x_3472_);
v___x_3476_ = v___x_3470_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_a_3474_);
v___x_3476_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
size_t v___x_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_add(v_i_3459_, v___x_3477_);
v___x_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3457_, v_sz_3458_, v___x_3478_, v___x_3476_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
return v___x_3479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3500_, lean_object* v_sz_3501_, lean_object* v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
size_t v_sz_boxed_3509_; size_t v_i_boxed_3510_; lean_object* v_res_3511_; 
v_sz_boxed_3509_ = lean_unbox_usize(v_sz_3501_);
lean_dec(v_sz_3501_);
v_i_boxed_3510_ = lean_unbox_usize(v_i_3502_);
lean_dec(v_i_3502_);
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3500_, v_sz_boxed_3509_, v_i_boxed_3510_, v_b_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_as_3500_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3512_, lean_object* v_init_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_root_3519_; lean_object* v_tail_3520_; lean_object* v___x_3521_; 
v_root_3519_ = lean_ctor_get(v_t_3512_, 0);
v_tail_3520_ = lean_ctor_get(v_t_3512_, 1);
lean_inc_ref(v_init_3513_);
v___x_3521_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3513_, v_root_3519_, v_init_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec_ref(v_init_3513_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3558_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3524_ = v___x_3521_;
v_isShared_3525_ = v_isSharedCheck_3558_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3558_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
if (lean_obj_tag(v_a_3522_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; 
v_a_3526_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v_a_3522_, 1);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v_a_3526_);
v___x_3528_ = v___x_3524_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; size_t v_sz_3533_; size_t v___x_3534_; lean_object* v___x_3535_; 
lean_del_object(v___x_3524_);
v_a_3530_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v_a_3522_, 1);
v___x_3531_ = lean_box(0);
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
lean_ctor_set(v___x_3532_, 1, v_a_3530_);
v_sz_3533_ = lean_array_size(v_tail_3520_);
v___x_3534_ = ((size_t)0ULL);
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3520_, v_sz_3533_, v___x_3534_, v___x_3532_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3549_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3538_ = v___x_3535_;
v_isShared_3539_ = v_isSharedCheck_3549_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3549_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_fst_3540_; 
v_fst_3540_ = lean_ctor_get(v_a_3536_, 0);
if (lean_obj_tag(v_fst_3540_) == 0)
{
lean_object* v_snd_3541_; lean_object* v___x_3543_; 
v_snd_3541_ = lean_ctor_get(v_a_3536_, 1);
lean_inc(v_snd_3541_);
lean_dec(v_a_3536_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v_snd_3541_);
v___x_3543_ = v___x_3538_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_snd_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
else
{
lean_object* v_val_3545_; lean_object* v___x_3547_; 
lean_inc_ref(v_fst_3540_);
lean_dec(v_a_3536_);
v_val_3545_ = lean_ctor_get(v_fst_3540_, 0);
lean_inc(v_val_3545_);
lean_dec_ref_known(v_fst_3540_, 1);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v_val_3545_);
v___x_3547_ = v___x_3538_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_val_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
v_a_3550_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3535_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3535_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v_a_3559_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3521_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3521_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3567_, lean_object* v_init_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3567_, v_init_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_t_3567_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_lctx_3580_; lean_object* v_decls_3581_; lean_object* v_result_3582_; lean_object* v___x_3583_; 
v_lctx_3580_ = lean_ctor_get(v_a_3575_, 2);
v_decls_3581_ = lean_ctor_get(v_lctx_3580_, 1);
v_result_3582_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3583_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3581_, v_result_3582_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Meta_getPropHyps(v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
return v_res_3589_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3594_ = l_Lean_MessageData_ofFormat(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3597_, lean_object* v___x_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; 
lean_inc(v___x_3598_);
lean_inc(v_mvarId_3597_);
v___x_3604_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3597_, v___x_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3605_; 
lean_dec_ref_known(v___x_3604_, 1);
lean_inc(v_mvarId_3597_);
v___x_3605_ = l_Lean_MVarId_getType(v_mvarId_3597_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3607_ = lean_box(0);
v___x_3608_ = l_Lean_Meta_synthInstance(v_a_3606_, v___x_3607_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
lean_inc(v_mvarId_3597_);
v___x_3610_ = l_Lean_mkMVar(v_mvarId_3597_);
v___x_3611_ = l_Lean_Meta_isExprDefEq(v___x_3610_, v_a_3609_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3623_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3623_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3623_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_unbox(v_a_3612_);
lean_dec(v_a_3612_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_del_object(v___x_3614_);
v___x_3617_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3618_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3598_, v_mvarId_3597_, v___x_3617_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
return v___x_3618_;
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_dec(v___x_3598_);
lean_dec(v_mvarId_3597_);
v___x_3619_ = lean_box(0);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v___x_3619_);
v___x_3621_ = v___x_3614_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v___x_3598_);
lean_dec(v_mvarId_3597_);
v_a_3624_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3611_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3611_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v___x_3598_);
lean_dec(v_mvarId_3597_);
v_a_3632_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3608_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3608_);
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
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v___x_3598_);
lean_dec(v_mvarId_3597_);
v_a_3640_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3605_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3605_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_dec(v___x_3598_);
lean_dec(v_mvarId_3597_);
return v___x_3604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3648_, lean_object* v___x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3648_, v___x_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v___f_3666_; lean_object* v___x_3667_; 
v___x_3665_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3659_);
v___f_3666_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3666_, 0, v_mvarId_3659_);
lean_closure_set(v___f_3666_, 1, v___x_3665_);
v___x_3667_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3659_, v___f_3666_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_MVarId_inferInstance(v_mvarId_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_3675_){
_start:
{
switch(lean_obj_tag(v_x_3675_))
{
case 0:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_unsigned_to_nat(0u);
return v___x_3676_;
}
case 1:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_unsigned_to_nat(1u);
return v___x_3677_;
}
default: 
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_unsigned_to_nat(2u);
return v___x_3678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_3679_);
lean_dec(v_x_3679_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3681_, lean_object* v_k_3682_){
_start:
{
if (lean_obj_tag(v_t_3681_) == 2)
{
lean_object* v_mvarId_3683_; lean_object* v___x_3684_; 
v_mvarId_3683_ = lean_ctor_get(v_t_3681_, 0);
lean_inc(v_mvarId_3683_);
lean_dec_ref_known(v_t_3681_, 1);
v___x_3684_ = lean_apply_1(v_k_3682_, v_mvarId_3683_);
return v___x_3684_;
}
else
{
lean_dec(v_t_3681_);
return v_k_3682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3685_, lean_object* v_ctorIdx_3686_, lean_object* v_t_3687_, lean_object* v_h_3688_, lean_object* v_k_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3687_, v_k_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3691_, lean_object* v_ctorIdx_3692_, lean_object* v_t_3693_, lean_object* v_h_3694_, lean_object* v_k_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3691_, v_ctorIdx_3692_, v_t_3693_, v_h_3694_, v_k_3695_);
lean_dec(v_ctorIdx_3692_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3697_, lean_object* v_closed_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3697_, v_closed_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3700_, lean_object* v_t_3701_, lean_object* v_h_3702_, lean_object* v_closed_3703_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3701_, v_closed_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3705_, lean_object* v_noChange_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3705_, v_noChange_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3708_, lean_object* v_t_3709_, lean_object* v_h_3710_, lean_object* v_noChange_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3709_, v_noChange_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3713_, lean_object* v_modified_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3713_, v_modified_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3716_, lean_object* v_t_3717_, lean_object* v_h_3718_, lean_object* v_modified_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3717_, v_modified_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v___y_3731_; uint8_t v___y_3732_; lean_object* v_a_3737_; lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_MVarId_getType(v_g_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3743_ = lean_unsigned_to_nat(1u);
v___x_3744_ = lean_mk_empty_array_with_capacity(v___x_3743_);
v___x_3745_ = lean_array_push(v___x_3744_, v_a_3741_);
v___x_3746_ = l_Lean_Meta_mkAppM(v___x_3742_, v___x_3745_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v___x_3748_ = lean_box(0);
v___x_3749_ = l_Lean_Meta_synthInstance(v_a_3747_, v___x_3748_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3758_; 
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v___x_3749_, 0);
lean_dec(v_unused_3759_);
v___x_3751_ = v___x_3749_;
v_isShared_3752_ = v_isSharedCheck_3758_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v___x_3749_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3758_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3753_ = 1;
v___x_3754_ = lean_box(v___x_3753_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 0, v___x_3754_);
v___x_3756_ = v___x_3751_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
else
{
lean_object* v_a_3760_; 
v_a_3760_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3749_, 1);
v_a_3737_ = v_a_3760_;
goto v___jp_3736_;
}
}
else
{
lean_object* v_a_3761_; 
v_a_3761_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3746_, 1);
v_a_3737_ = v_a_3761_;
goto v___jp_3736_;
}
}
else
{
lean_object* v_a_3762_; 
v_a_3762_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3740_, 1);
v_a_3737_ = v_a_3762_;
goto v___jp_3736_;
}
v___jp_3730_:
{
if (v___y_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec_ref(v___y_3731_);
v___x_3733_ = lean_box(v___y_3732_);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___y_3731_);
return v___x_3735_;
}
}
v___jp_3736_:
{
uint8_t v___x_3738_; 
v___x_3738_ = l_Lean_Exception_isInterrupt(v_a_3737_);
if (v___x_3738_ == 0)
{
uint8_t v___x_3739_; 
lean_inc_ref(v_a_3737_);
v___x_3739_ = l_Lean_Exception_isRuntime(v_a_3737_);
v___y_3731_ = v_a_3737_;
v___y_3732_ = v___x_3739_;
goto v___jp_3730_;
}
else
{
v___y_3731_ = v_a_3737_;
v___y_3732_ = v___x_3738_;
goto v___jp_3730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_MVarId_isSubsingleton(v_g_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3790_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3787_, v___x_3788_, v___x_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3792_;
}
}
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
