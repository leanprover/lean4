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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl___boxed(lean_object*);
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
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_box(0);
v___x_104_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_95_, v_mvarId_90_, v_tag_91_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_cache_96_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_zetaDeltaFVarIds_97_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v_postponed_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v_diag_99_);
v___x_106_ = v_reuseFailAlloc_109_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_st_ref_put(v_a_92_, v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_103_);
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
lean_object* v___x_233_; lean_object* v_env_234_; uint8_t v___x_235_; lean_object* v_env_236_; lean_object* v___x_237_; lean_object* v_toCold_238_; lean_object* v_mctx_239_; lean_object* v_lctx_240_; lean_object* v_options_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
v___x_235_ = 0;
v_env_236_ = l_Lean_Environment_setRecordingDeps(v_env_234_, v___x_235_);
v___x_237_ = lean_st_ref_get(v___y_229_);
v_toCold_238_ = lean_ctor_get(v___y_230_, 0);
v_mctx_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_mctx_239_);
lean_dec(v___x_237_);
v_lctx_240_ = lean_ctor_get(v___y_228_, 2);
v_options_241_ = lean_ctor_get(v_toCold_238_, 2);
lean_inc_ref(v_options_241_);
lean_inc_ref(v_lctx_240_);
v___x_242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_242_, 0, v_env_236_);
lean_ctor_set(v___x_242_, 1, v_mctx_239_);
lean_ctor_set(v___x_242_, 2, v_lctx_240_);
lean_ctor_set(v___x_242_, 3, v_options_241_);
v___x_243_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_msgData_227_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_ref_258_; lean_object* v___x_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_ref_258_ = lean_ctor_get(v___y_255_, 2);
v___x_259_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_inc(v_ref_258_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_ref_258_);
lean_ctor_set(v___x_264_, 1, v_a_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 1);
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_279_, lean_object* v_mvarId_280_, lean_object* v_msg_x3f_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
if (lean_obj_tag(v_msg_x3f_281_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_287_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_288_ = l_Lean_MessageData_ofName(v_tacticName_279_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_mvarId_280_);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_293_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_val_295_ = lean_ctor_get(v_msg_x3f_281_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v_msg_x3f_281_, 1);
v___x_296_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_279_, v_mvarId_280_, v_val_295_);
v___x_297_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_296_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_298_, lean_object* v_mvarId_299_, lean_object* v_msg_x3f_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_298_, v_mvarId_299_, v_msg_x3f_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_307_, lean_object* v_tacticName_308_, lean_object* v_mvarId_309_, lean_object* v_msg_x3f_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_308_, v_mvarId_309_, v_msg_x3f_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_317_, lean_object* v_tacticName_318_, lean_object* v_mvarId_319_, lean_object* v_msg_x3f_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_317_, v_tacticName_318_, v_mvarId_319_, v_msg_x3f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_327_, lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_335_, v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_349_, lean_object* v_ex_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_nestedMsg_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_msg_362_; lean_object* v_kind_363_; uint8_t v___x_364_; 
v_nestedMsg_356_ = l_Lean_Exception_toMessageData(v_ex_350_);
v___x_357_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_358_ = l_Lean_MessageData_ofName(v_tacticName_349_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_inc_ref(v_nestedMsg_356_);
v_msg_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_362_, 0, v___x_361_);
lean_ctor_set(v_msg_362_, 1, v_nestedMsg_356_);
v_kind_363_ = l_Lean_MessageData_kind(v_nestedMsg_356_);
lean_dec_ref(v_nestedMsg_356_);
v___x_364_ = l_Lean_Name_isAnonymous(v_kind_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_366_ = l_Lean_Name_append(v___x_365_, v_kind_363_);
v___x_367_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_msg_362_);
v___x_368_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_367_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
lean_dec(v_kind_363_);
v___x_369_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_362_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_370_, lean_object* v_ex_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_370_, v_ex_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_378_, lean_object* v_tacticName_379_, lean_object* v_ex_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_379_, v_ex_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_387_, lean_object* v_tacticName_388_, lean_object* v_ex_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_387_, v_tacticName_388_, v_ex_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
return v_res_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_396_, lean_object* v_i_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = lean_array_get_size(v_keys_396_);
v___x_400_ = lean_nat_dec_lt(v_i_397_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v_i_397_);
return v___x_400_;
}
else
{
lean_object* v_k_x27_401_; uint8_t v___x_402_; 
v_k_x27_401_ = lean_array_fget_borrowed(v_keys_396_, v_i_397_);
v___x_402_ = l_Lean_instBEqMVarId_beq(v_k_398_, v_k_x27_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_i_397_, v___x_403_);
lean_dec(v_i_397_);
v_i_397_ = v___x_404_;
goto _start;
}
else
{
lean_dec(v_i_397_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_406_, v_i_407_, v_k_408_);
lean_dec(v_k_408_);
lean_dec_ref(v_keys_406_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_411_, size_t v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v_es_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v_j_418_; lean_object* v___x_419_; 
v_es_414_ = lean_ctor_get(v_x_411_, 0);
v___x_415_ = lean_box(2);
v___x_416_ = ((size_t)31ULL);
v___x_417_ = lean_usize_land(v_x_412_, v___x_416_);
v_j_418_ = lean_usize_to_nat(v___x_417_);
v___x_419_ = lean_array_get_borrowed(v___x_415_, v_es_414_, v_j_418_);
lean_dec(v_j_418_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_key_420_; uint8_t v___x_421_; 
v_key_420_ = lean_ctor_get(v___x_419_, 0);
v___x_421_ = l_Lean_instBEqMVarId_beq(v_x_413_, v_key_420_);
return v___x_421_;
}
case 1:
{
lean_object* v_node_422_; size_t v___x_423_; size_t v___x_424_; 
v_node_422_ = lean_ctor_get(v___x_419_, 0);
v___x_423_ = ((size_t)5ULL);
v___x_424_ = lean_usize_shift_right(v_x_412_, v___x_423_);
v_x_411_ = v_node_422_;
v_x_412_ = v___x_424_;
goto _start;
}
default: 
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_ks_427_ = lean_ctor_get(v_x_411_, 0);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_427_, v___x_428_, v_x_413_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
size_t v_x_546__boxed_433_; uint8_t v_res_434_; lean_object* v_r_435_; 
v_x_546__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_430_, v_x_546__boxed_433_, v_x_432_);
lean_dec(v_x_432_);
lean_dec_ref(v_x_430_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___x_438_; size_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = l_Lean_instHashableMVarId_hash(v_x_437_);
v___x_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_436_, v___x_439_, v_x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_441_, v_x_442_);
lean_dec(v_x_442_);
lean_dec_ref(v_x_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_mctx_449_; lean_object* v_eAssignment_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = lean_st_ref_get(v___y_446_);
v_mctx_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_mctx_449_);
lean_dec(v___x_448_);
v_eAssignment_450_ = lean_ctor_get(v_mctx_449_, 8);
lean_inc_ref(v_eAssignment_450_);
lean_dec_ref(v_mctx_449_);
v___x_451_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_450_, v_mvarId_445_);
lean_dec_ref(v_eAssignment_450_);
v___x_452_ = lean_box(v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec(v_mvarId_454_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_465_ = l_Lean_MessageData_ofFormat(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_467_ = l_Lean_MessageData_note(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_469_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_473_, lean_object* v_tacticName_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_492_; 
v___x_480_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_473_, v_a_476_);
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_492_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = lean_unbox(v_a_481_);
lean_dec(v_a_481_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec(v_tacticName_474_);
lean_dec(v_mvarId_473_);
v___x_486_ = lean_box(0);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_del_object(v___x_483_);
v___x_490_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_491_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_474_, v_mvarId_473_, v___x_490_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_493_, lean_object* v_tacticName_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_493_, v_tacticName_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_501_, v___y_503_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v_mvarId_508_);
return v_res_514_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_519_, v_x_520_, v_x_521_);
lean_dec(v_x_521_);
lean_dec_ref(v_x_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_524_, lean_object* v_x_525_, size_t v_x_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_525_, v_x_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
size_t v_x_713__boxed_533_; uint8_t v_res_534_; lean_object* v_r_535_; 
v_x_713__boxed_533_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_529_, v_x_530_, v_x_713__boxed_533_, v_x_532_);
lean_dec(v_x_532_);
lean_dec_ref(v_x_530_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_536_, lean_object* v_keys_537_, lean_object* v_vals_538_, lean_object* v_heq_539_, lean_object* v_i_540_, lean_object* v_k_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_537_, v_i_540_, v_k_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_543_, lean_object* v_keys_544_, lean_object* v_vals_545_, lean_object* v_heq_546_, lean_object* v_i_547_, lean_object* v_k_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_543_, v_keys_544_, v_vals_545_, v_heq_546_, v_i_547_, v_k_548_);
lean_dec(v_k_548_);
lean_dec_ref(v_vals_545_);
lean_dec_ref(v_keys_544_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_MVarId_getDecl(v_mvarId_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_566_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_566_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_type_562_; lean_object* v___x_564_; 
v_type_562_ = lean_ctor_get(v_a_558_, 2);
lean_inc_ref(v_type_562_);
lean_dec(v_a_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_type_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_type_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_557_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_557_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_MVarId_getType(v_mvarId_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = l_Lean_Expr_hasMVar(v_e_582_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v_e_582_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v_mctx_588_; lean_object* v___x_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; lean_object* v_cache_593_; lean_object* v_zetaDeltaFVarIds_594_; lean_object* v_postponed_595_; lean_object* v_diag_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v___x_587_ = lean_st_ref_get(v___y_583_);
v_mctx_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_mctx_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_instantiateMVarsCore(v_mctx_588_, v_e_582_);
v_fst_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_snd_591_);
lean_dec_ref(v___x_589_);
v___x_592_ = lean_st_ref_take(v___y_583_);
v_cache_593_ = lean_ctor_get(v___x_592_, 1);
v_zetaDeltaFVarIds_594_ = lean_ctor_get(v___x_592_, 2);
v_postponed_595_ = lean_ctor_get(v___x_592_, 3);
v_diag_596_ = lean_ctor_get(v___x_592_, 4);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_606_);
v___x_598_ = v___x_592_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_diag_596_);
lean_inc(v_postponed_595_);
lean_inc(v_zetaDeltaFVarIds_594_);
lean_inc(v_cache_593_);
lean_dec(v___x_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_snd_591_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_snd_591_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_cache_593_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_zetaDeltaFVarIds_594_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_postponed_595_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_diag_596_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_st_ref_put(v___y_583_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v_fst_590_);
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_607_, v___y_608_);
lean_dec(v___y_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_611_, v___y_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_MVarId_getType(v_mvarId_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
lean_inc(v_a_629_);
lean_inc_ref(v_a_628_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
v___x_633_ = lean_whnf(v_a_632_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_634_, v_a_627_);
return v___x_635_;
}
else
{
return v___x_633_;
}
}
else
{
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_MVarId_getType_x27(v_mvarId_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_709_ = 0;
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_711_ = l_Lean_registerTraceClass(v___x_708_, v___x_709_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_738_, lean_object* v_x_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_738_, v_x_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_746_, lean_object* v_mvarId_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_747_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_755_, lean_object* v_mvarId_756_, lean_object* v_x_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_755_, v_mvarId_756_, v_x_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v_ks_768_; lean_object* v_vs_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_793_; 
v_ks_768_ = lean_ctor_get(v_x_764_, 0);
v_vs_769_ = lean_ctor_get(v_x_764_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_793_ == 0)
{
v___x_771_ = v_x_764_;
v_isShared_772_ = v_isSharedCheck_793_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_vs_769_);
lean_inc(v_ks_768_);
lean_dec(v_x_764_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_793_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_array_get_size(v_ks_768_);
v___x_774_ = lean_nat_dec_lt(v_x_765_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec(v_x_765_);
v___x_775_ = lean_array_push(v_ks_768_, v_x_766_);
v___x_776_ = lean_array_push(v_vs_769_, v_x_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_776_);
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
lean_object* v_k_x27_780_; uint8_t v___x_781_; 
v_k_x27_780_ = lean_array_fget_borrowed(v_ks_768_, v_x_765_);
v___x_781_ = l_Lean_instBEqMVarId_beq(v_x_766_, v_k_x27_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_783_; 
if (v_isShared_772_ == 0)
{
v___x_783_ = v___x_771_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_ks_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_vs_769_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_x_765_, v___x_784_);
lean_dec(v_x_765_);
v_x_764_ = v___x_783_;
v_x_765_ = v___x_785_;
goto _start;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = lean_array_fset(v_ks_768_, v_x_765_, v_x_766_);
v___x_789_ = lean_array_fset(v_vs_769_, v_x_765_, v_x_767_);
lean_dec(v_x_765_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_789_);
lean_ctor_set(v___x_771_, 0, v___x_788_);
v___x_791_ = v___x_771_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_794_, lean_object* v_k_795_, lean_object* v_v_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_794_, v___x_797_, v_k_795_, v_v_796_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_800_, size_t v_x_801_, size_t v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
lean_object* v_es_805_; size_t v___x_806_; size_t v___x_807_; lean_object* v_j_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_es_805_ = lean_ctor_get(v_x_800_, 0);
v___x_806_ = ((size_t)31ULL);
v___x_807_ = lean_usize_land(v_x_801_, v___x_806_);
v_j_808_ = lean_usize_to_nat(v___x_807_);
v___x_809_ = lean_array_get_size(v_es_805_);
v___x_810_ = lean_nat_dec_lt(v_j_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_dec(v_j_808_);
lean_dec(v_x_804_);
lean_dec(v_x_803_);
return v_x_800_;
}
else
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_849_; 
lean_inc_ref(v_es_805_);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_x_800_, 0);
lean_dec(v_unused_850_);
v___x_812_ = v_x_800_;
v_isShared_813_ = v_isSharedCheck_849_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_849_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_v_814_; lean_object* v___x_815_; lean_object* v_xs_x27_816_; lean_object* v___y_818_; 
v_v_814_ = lean_array_fget(v_es_805_, v_j_808_);
v___x_815_ = lean_box(0);
v_xs_x27_816_ = lean_array_fset(v_es_805_, v_j_808_, v___x_815_);
switch(lean_obj_tag(v_v_814_))
{
case 0:
{
lean_object* v_key_823_; lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_key_823_ = lean_ctor_get(v_v_814_, 0);
v_val_824_ = lean_ctor_get(v_v_814_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_v_814_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v_v_814_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_inc(v_key_823_);
lean_dec(v_v_814_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_instBEqMVarId_beq(v_x_803_, v_key_823_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_826_);
v___x_829_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_823_, v_val_824_, v_x_803_, v_x_804_);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
v___y_818_ = v___x_830_;
goto v___jp_817_;
}
else
{
lean_object* v___x_832_; 
lean_dec(v_val_824_);
lean_dec(v_key_823_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_x_804_);
lean_ctor_set(v___x_826_, 0, v_x_803_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_x_803_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_x_804_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v___y_818_ = v___x_832_;
goto v___jp_817_;
}
}
}
}
case 1:
{
lean_object* v_node_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_847_; 
v_node_835_ = lean_ctor_get(v_v_814_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_v_814_);
if (v_isSharedCheck_847_ == 0)
{
v___x_837_ = v_v_814_;
v_isShared_838_ = v_isSharedCheck_847_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_node_835_);
lean_dec(v_v_814_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_847_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_839_ = ((size_t)5ULL);
v___x_840_ = lean_usize_shift_right(v_x_801_, v___x_839_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_x_802_, v___x_841_);
v___x_843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_835_, v___x_840_, v___x_842_, v_x_803_, v_x_804_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_843_);
v___x_845_ = v___x_837_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v___y_818_ = v___x_845_;
goto v___jp_817_;
}
}
}
default: 
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_x_803_);
lean_ctor_set(v___x_848_, 1, v_x_804_);
v___y_818_ = v___x_848_;
goto v___jp_817_;
}
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_array_fset(v_xs_x27_816_, v_j_808_, v___y_818_);
lean_dec(v_j_808_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
else
{
lean_object* v_ks_851_; lean_object* v_vs_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_870_; 
v_ks_851_ = lean_ctor_get(v_x_800_, 0);
v_vs_852_ = lean_ctor_get(v_x_800_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_870_ == 0)
{
v___x_854_ = v_x_800_;
v_isShared_855_ = v_isSharedCheck_870_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_vs_852_);
lean_inc(v_ks_851_);
lean_dec(v_x_800_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_870_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_ks_851_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_vs_852_);
v___x_857_ = v_reuseFailAlloc_869_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v_newNode_858_; size_t v___x_859_; uint8_t v___x_860_; 
v_newNode_858_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_857_, v_x_803_, v_x_804_);
v___x_859_ = ((size_t)7ULL);
v___x_860_ = lean_usize_dec_le(v___x_859_, v_x_802_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_858_);
v___x_862_ = lean_unsigned_to_nat(4u);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
lean_dec(v___x_861_);
if (v___x_863_ == 0)
{
lean_object* v_ks_864_; lean_object* v_vs_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_ks_864_ = lean_ctor_get(v_newNode_858_, 0);
lean_inc_ref(v_ks_864_);
v_vs_865_ = lean_ctor_get(v_newNode_858_, 1);
lean_inc_ref(v_vs_865_);
lean_dec_ref(v_newNode_858_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_802_, v_ks_864_, v_vs_865_, v___x_866_, v___x_867_);
lean_dec_ref(v_vs_865_);
lean_dec_ref(v_ks_864_);
return v___x_868_;
}
else
{
return v_newNode_858_;
}
}
else
{
return v_newNode_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_i_874_, lean_object* v_entries_875_){
_start:
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_array_get_size(v_keys_872_);
v___x_877_ = lean_nat_dec_lt(v_i_874_, v___x_876_);
if (v___x_877_ == 0)
{
lean_dec(v_i_874_);
return v_entries_875_;
}
else
{
lean_object* v_k_878_; lean_object* v_v_879_; uint64_t v___x_880_; size_t v_h_881_; size_t v___x_882_; lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v_h_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_k_878_ = lean_array_fget_borrowed(v_keys_872_, v_i_874_);
v_v_879_ = lean_array_fget_borrowed(v_vals_873_, v_i_874_);
v___x_880_ = l_Lean_instHashableMVarId_hash(v_k_878_);
v_h_881_ = lean_uint64_to_usize(v___x_880_);
v___x_882_ = ((size_t)5ULL);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_sub(v_depth_871_, v___x_884_);
v___x_886_ = lean_usize_mul(v___x_882_, v___x_885_);
v_h_887_ = lean_usize_shift_right(v_h_881_, v___x_886_);
v___x_888_ = lean_nat_add(v_i_874_, v___x_883_);
lean_dec(v_i_874_);
lean_inc(v_v_879_);
lean_inc(v_k_878_);
v___x_889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_875_, v_h_887_, v_depth_871_, v_k_878_, v_v_879_);
v_i_874_ = v___x_888_;
v_entries_875_ = v___x_889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_891_, lean_object* v_keys_892_, lean_object* v_vals_893_, lean_object* v_i_894_, lean_object* v_entries_895_){
_start:
{
size_t v_depth_boxed_896_; lean_object* v_res_897_; 
v_depth_boxed_896_ = lean_unbox_usize(v_depth_891_);
lean_dec(v_depth_891_);
v_res_897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_896_, v_keys_892_, v_vals_893_, v_i_894_, v_entries_895_);
lean_dec_ref(v_vals_893_);
lean_dec_ref(v_keys_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
size_t v_x_1022__boxed_903_; size_t v_x_1023__boxed_904_; lean_object* v_res_905_; 
v_x_1022__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_x_1023__boxed_904_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_898_, v_x_1022__boxed_903_, v_x_1023__boxed_904_, v_x_901_, v_x_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
uint64_t v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v___x_909_ = l_Lean_instHashableMVarId_hash(v_x_907_);
v___x_910_ = lean_uint64_to_usize(v___x_909_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_906_, v___x_910_, v___x_911_, v_x_907_, v_x_908_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_913_, lean_object* v_val_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v_mctx_918_; lean_object* v_cache_919_; lean_object* v_zetaDeltaFVarIds_920_; lean_object* v_postponed_921_; lean_object* v_diag_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_952_; 
v___x_917_ = lean_st_ref_take(v___y_915_);
v_mctx_918_ = lean_ctor_get(v___x_917_, 0);
v_cache_919_ = lean_ctor_get(v___x_917_, 1);
v_zetaDeltaFVarIds_920_ = lean_ctor_get(v___x_917_, 2);
v_postponed_921_ = lean_ctor_get(v___x_917_, 3);
v_diag_922_ = lean_ctor_get(v___x_917_, 4);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_952_ == 0)
{
v___x_924_ = v___x_917_;
v_isShared_925_ = v_isSharedCheck_952_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_diag_922_);
lean_inc(v_postponed_921_);
lean_inc(v_zetaDeltaFVarIds_920_);
lean_inc(v_cache_919_);
lean_inc(v_mctx_918_);
lean_dec(v___x_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_952_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_depth_926_; lean_object* v_levelAssignDepth_927_; lean_object* v_lmvarCounter_928_; lean_object* v_mvarCounter_929_; lean_object* v_lDecls_930_; lean_object* v_decls_931_; lean_object* v_userNames_932_; lean_object* v_lAssignment_933_; lean_object* v_eAssignment_934_; lean_object* v_dAssignment_935_; lean_object* v_instanceTypedMVars_936_; lean_object* v_synthNormMemo_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_951_; 
v_depth_926_ = lean_ctor_get(v_mctx_918_, 0);
v_levelAssignDepth_927_ = lean_ctor_get(v_mctx_918_, 1);
v_lmvarCounter_928_ = lean_ctor_get(v_mctx_918_, 2);
v_mvarCounter_929_ = lean_ctor_get(v_mctx_918_, 3);
v_lDecls_930_ = lean_ctor_get(v_mctx_918_, 4);
v_decls_931_ = lean_ctor_get(v_mctx_918_, 5);
v_userNames_932_ = lean_ctor_get(v_mctx_918_, 6);
v_lAssignment_933_ = lean_ctor_get(v_mctx_918_, 7);
v_eAssignment_934_ = lean_ctor_get(v_mctx_918_, 8);
v_dAssignment_935_ = lean_ctor_get(v_mctx_918_, 9);
v_instanceTypedMVars_936_ = lean_ctor_get(v_mctx_918_, 10);
v_synthNormMemo_937_ = lean_ctor_get(v_mctx_918_, 11);
v_isSharedCheck_951_ = !lean_is_exclusive(v_mctx_918_);
if (v_isSharedCheck_951_ == 0)
{
v___x_939_ = v_mctx_918_;
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_synthNormMemo_937_);
lean_inc(v_instanceTypedMVars_936_);
lean_inc(v_dAssignment_935_);
lean_inc(v_eAssignment_934_);
lean_inc(v_lAssignment_933_);
lean_inc(v_userNames_932_);
lean_inc(v_decls_931_);
lean_inc(v_lDecls_930_);
lean_inc(v_mvarCounter_929_);
lean_inc(v_lmvarCounter_928_);
lean_inc(v_levelAssignDepth_927_);
lean_inc(v_depth_926_);
lean_dec(v_mctx_918_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_934_, v_mvarId_913_, v_val_914_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 8, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_depth_926_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_levelAssignDepth_927_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_lmvarCounter_928_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_mvarCounter_929_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_lDecls_930_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_decls_931_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_userNames_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_lAssignment_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 9, v_dAssignment_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 10, v_instanceTypedMVars_936_);
lean_ctor_set(v_reuseFailAlloc_950_, 11, v_synthNormMemo_937_);
v___x_944_ = v_reuseFailAlloc_950_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_944_);
v___x_946_ = v___x_924_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_cache_919_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_zetaDeltaFVarIds_920_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_postponed_921_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_diag_922_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_st_ref_put(v___y_915_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_941_);
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
lean_dec_ref_known(v___x_966_, 1);
lean_inc(v_mvarId_958_);
v___x_967_ = l_Lean_MVarId_getType(v_mvarId_958_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = 1;
v___x_970_ = l_Lean_Meta_mkLabeledSorry(v_a_968_, v_synthetic_960_, v___x_969_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_958_, v_a_971_, v___y_962_);
return v___x_972_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
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
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
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
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
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
size_t v_x_1343__boxed_1056_; size_t v_x_1344__boxed_1057_; lean_object* v_res_1058_; 
v_x_1343__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_x_1344__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1050_, v_x_1051_, v_x_1343__boxed_1056_, v_x_1344__boxed_1057_, v_x_1054_, v_x_1055_);
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
lean_dec_ref_known(v___x_1093_, 1);
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
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_Expr_fvarId_x21(v_e_1177_);
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1184_, v___x_1186_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_st_ref_put(v___y_1178_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_visited_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1218_ = lean_st_ref_get(v_a_1216_);
v_visited_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref(v_visited_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = lean_ptr_addr(v_e_1215_);
v___x_1221_ = ((size_t)8191ULL);
v___x_1222_ = lean_usize_mod(v___x_1220_, v___x_1221_);
v___x_1223_ = lean_array_uget(v_visited_1219_, v___x_1222_);
lean_dec_ref(v_visited_1219_);
v___x_1224_ = lean_ptr_addr(v___x_1223_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_usize_dec_eq(v___x_1224_, v___x_1220_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v_visited_1227_; lean_object* v_checked_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1239_; 
v___x_1226_ = lean_st_ref_take(v_a_1216_);
v_visited_1227_ = lean_ctor_get(v___x_1226_, 0);
v_checked_1228_ = lean_ctor_get(v___x_1226_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1230_ = v___x_1226_;
v_isShared_1231_ = v_isSharedCheck_1239_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_checked_1228_);
lean_inc(v_visited_1227_);
lean_dec(v___x_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1239_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_array_uset(v_visited_1227_, v___x_1222_, v_e_1215_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_checked_1228_);
v___x_1234_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_st_ref_put(v_a_1216_, v___x_1234_);
v___x_1236_ = lean_box(v___x_1225_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v_e_1215_);
v___x_1240_ = lean_box(v___x_1225_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1242_, lean_object* v_a_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1242_, v_a_1243_);
lean_dec(v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = 0;
return v___x_1248_;
}
else
{
lean_object* v_key_1249_; lean_object* v_tail_1250_; uint8_t v___x_1251_; 
v_key_1249_ = lean_ctor_get(v_x_1247_, 0);
v_tail_1250_ = lean_ctor_get(v_x_1247_, 2);
v___x_1251_ = lean_expr_eqv(v_key_1249_, v_a_1246_);
if (v___x_1251_ == 0)
{
v_x_1247_ = v_tail_1250_;
goto _start;
}
else
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_a_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
return v_x_1257_;
}
else
{
lean_object* v_key_1259_; lean_object* v_value_1260_; lean_object* v_tail_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1284_; 
v_key_1259_ = lean_ctor_get(v_x_1258_, 0);
v_value_1260_ = lean_ctor_get(v_x_1258_, 1);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 2);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1263_ = v_x_1258_;
v_isShared_1264_ = v_isSharedCheck_1284_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_tail_1261_);
lean_inc(v_value_1260_);
lean_inc(v_key_1259_);
lean_dec(v_x_1258_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1284_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; uint64_t v_fold_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1265_ = lean_array_get_size(v_x_1257_);
v___x_1266_ = l_Lean_Expr_hash(v_key_1259_);
v___x_1267_ = 32ULL;
v___x_1268_ = lean_uint64_shift_right(v___x_1266_, v___x_1267_);
v_fold_1269_ = lean_uint64_xor(v___x_1266_, v___x_1268_);
v___x_1270_ = 16ULL;
v___x_1271_ = lean_uint64_shift_right(v_fold_1269_, v___x_1270_);
v___x_1272_ = lean_uint64_xor(v_fold_1269_, v___x_1271_);
v___x_1273_ = lean_uint64_to_usize(v___x_1272_);
v___x_1274_ = lean_usize_of_nat(v___x_1265_);
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_sub(v___x_1274_, v___x_1275_);
v___x_1277_ = lean_usize_land(v___x_1273_, v___x_1276_);
v___x_1278_ = lean_array_uget_borrowed(v_x_1257_, v___x_1277_);
lean_inc(v___x_1278_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 2, v___x_1278_);
v___x_1280_ = v___x_1263_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_key_1259_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_value_1260_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_array_uset(v_x_1257_, v___x_1277_, v___x_1280_);
v_x_1257_ = v___x_1281_;
v_x_1258_ = v_tail_1261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1285_, lean_object* v_source_1286_, lean_object* v_target_1287_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_array_get_size(v_source_1286_);
v___x_1289_ = lean_nat_dec_lt(v_i_1285_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v_source_1286_);
lean_dec(v_i_1285_);
return v_target_1287_;
}
else
{
lean_object* v_es_1290_; lean_object* v___x_1291_; lean_object* v_source_1292_; lean_object* v_target_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_es_1290_ = lean_array_fget(v_source_1286_, v_i_1285_);
v___x_1291_ = lean_box(0);
v_source_1292_ = lean_array_fset(v_source_1286_, v_i_1285_, v___x_1291_);
v_target_1293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1287_, v_es_1290_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_i_1285_, v___x_1294_);
lean_dec(v_i_1285_);
v_i_1285_ = v___x_1295_;
v_source_1286_ = v_source_1292_;
v_target_1287_ = v_target_1293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_nbuckets_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1298_ = lean_array_get_size(v_data_1297_);
v___x_1299_ = lean_unsigned_to_nat(2u);
v_nbuckets_1300_ = lean_nat_mul(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_mk_array(v_nbuckets_1300_, v___x_1302_);
v___x_1304_ = lean_array_propagate_mark(v_data_1297_, v___x_1303_);
v___x_1305_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1301_, v_data_1297_, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1306_, lean_object* v_a_1307_, lean_object* v_b_1308_){
_start:
{
lean_object* v_size_1309_; lean_object* v_buckets_1310_; lean_object* v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v_fold_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; lean_object* v_bkt_1324_; uint8_t v___x_1325_; 
v_size_1309_ = lean_ctor_get(v_m_1306_, 0);
v_buckets_1310_ = lean_ctor_get(v_m_1306_, 1);
v___x_1311_ = lean_array_get_size(v_buckets_1310_);
v___x_1312_ = l_Lean_Expr_hash(v_a_1307_);
v___x_1313_ = 32ULL;
v___x_1314_ = lean_uint64_shift_right(v___x_1312_, v___x_1313_);
v_fold_1315_ = lean_uint64_xor(v___x_1312_, v___x_1314_);
v___x_1316_ = 16ULL;
v___x_1317_ = lean_uint64_shift_right(v_fold_1315_, v___x_1316_);
v___x_1318_ = lean_uint64_xor(v_fold_1315_, v___x_1317_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = lean_usize_of_nat(v___x_1311_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_sub(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_usize_land(v___x_1319_, v___x_1322_);
v_bkt_1324_ = lean_array_uget_borrowed(v_buckets_1310_, v___x_1323_);
v___x_1325_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1307_, v_bkt_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1346_; 
lean_inc_ref(v_buckets_1310_);
lean_inc(v_size_1309_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_m_1306_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; 
v_unused_1347_ = lean_ctor_get(v_m_1306_, 1);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_m_1306_, 0);
lean_dec(v_unused_1348_);
v___x_1327_ = v_m_1306_;
v_isShared_1328_ = v_isSharedCheck_1346_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_m_1306_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1346_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v_size_x27_1330_; lean_object* v___x_1331_; lean_object* v_buckets_x27_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
v_size_x27_1330_ = lean_nat_add(v_size_1309_, v___x_1329_);
lean_dec(v_size_1309_);
lean_inc(v_bkt_1324_);
v___x_1331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1307_);
lean_ctor_set(v___x_1331_, 1, v_b_1308_);
lean_ctor_set(v___x_1331_, 2, v_bkt_1324_);
v_buckets_x27_1332_ = lean_array_uset(v_buckets_1310_, v___x_1323_, v___x_1331_);
v___x_1333_ = lean_unsigned_to_nat(4u);
v___x_1334_ = lean_nat_mul(v_size_x27_1330_, v___x_1333_);
v___x_1335_ = lean_unsigned_to_nat(3u);
v___x_1336_ = lean_nat_div(v___x_1334_, v___x_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_array_get_size(v_buckets_x27_1332_);
v___x_1338_ = lean_nat_dec_le(v___x_1336_, v___x_1337_);
lean_dec(v___x_1336_);
if (v___x_1338_ == 0)
{
lean_object* v_val_1339_; lean_object* v___x_1341_; 
v_val_1339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1332_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_val_1339_);
lean_ctor_set(v___x_1327_, 0, v_size_x27_1330_);
v___x_1341_ = v___x_1327_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_size_x27_1330_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_val_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v___x_1344_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_buckets_x27_1332_);
lean_ctor_set(v___x_1327_, 0, v_size_x27_1330_);
v___x_1344_ = v___x_1327_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_size_x27_1330_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_buckets_x27_1332_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_dec(v_b_1308_);
lean_dec_ref(v_a_1307_);
return v_m_1306_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_buckets_1351_; lean_object* v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v_fold_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_buckets_1351_ = lean_ctor_get(v_m_1349_, 1);
v___x_1352_ = lean_array_get_size(v_buckets_1351_);
v___x_1353_ = l_Lean_Expr_hash(v_a_1350_);
v___x_1354_ = 32ULL;
v___x_1355_ = lean_uint64_shift_right(v___x_1353_, v___x_1354_);
v_fold_1356_ = lean_uint64_xor(v___x_1353_, v___x_1355_);
v___x_1357_ = 16ULL;
v___x_1358_ = lean_uint64_shift_right(v_fold_1356_, v___x_1357_);
v___x_1359_ = lean_uint64_xor(v_fold_1356_, v___x_1358_);
v___x_1360_ = lean_uint64_to_usize(v___x_1359_);
v___x_1361_ = lean_usize_of_nat(v___x_1352_);
v___x_1362_ = ((size_t)1ULL);
v___x_1363_ = lean_usize_sub(v___x_1361_, v___x_1362_);
v___x_1364_ = lean_usize_land(v___x_1360_, v___x_1363_);
v___x_1365_ = lean_array_uget_borrowed(v_buckets_1351_, v___x_1364_);
v___x_1366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1350_, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1367_, lean_object* v_a_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1367_, v_a_1368_);
lean_dec_ref(v_a_1368_);
lean_dec_ref(v_m_1367_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_checked_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_st_ref_get(v_a_1372_);
v_checked_1375_ = lean_ctor_get(v___x_1374_, 1);
lean_inc_ref(v_checked_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1375_, v_e_1371_);
lean_dec_ref(v_checked_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v_visited_1378_; lean_object* v_checked_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1391_; 
v___x_1377_ = lean_st_ref_take(v_a_1372_);
v_visited_1378_ = lean_ctor_get(v___x_1377_, 0);
v_checked_1379_ = lean_ctor_get(v___x_1377_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1381_ = v___x_1377_;
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_checked_1379_);
lean_inc(v_visited_1378_);
lean_dec(v___x_1377_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1379_, v_e_1371_, v___x_1383_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_visited_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_st_ref_put(v_a_1372_, v___x_1386_);
v___x_1388_ = lean_box(v___x_1376_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_e_1371_);
v___x_1392_ = lean_box(v___x_1376_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1394_, v_a_1395_);
lean_dec(v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1398_, lean_object* v_f_1399_, uint8_t v_stopWhenVisited_1400_, lean_object* v_e_1401_, lean_object* v_a_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v_d_1415_; lean_object* v_b_1416_; lean_object* v___y_1417_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___x_1447_; 
lean_inc_ref(v_e_1401_);
v___x_1447_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1401_, v_a_1402_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1480_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_del_object(v___x_1450_);
lean_inc_ref(v_p_1398_);
lean_inc_ref(v_e_1401_);
v___x_1453_ = lean_apply_1(v_p_1398_, v_e_1401_);
v___x_1454_ = lean_unbox(v___x_1453_);
if (v___x_1454_ == 0)
{
v___y_1421_ = v_a_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1455_; 
lean_inc_ref(v_e_1401_);
v___x_1455_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1401_, v_a_1402_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; uint8_t v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = lean_unbox(v_a_1456_);
lean_dec(v_a_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
lean_inc_ref(v_f_1399_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v_e_1401_);
v___x_1458_ = lean_apply_7(v_f_1399_, v_e_1401_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, lean_box(0));
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v___x_1458_, 0);
lean_dec(v_unused_1467_);
v___x_1460_ = v___x_1458_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v___x_1458_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
if (v_stopWhenVisited_1400_ == 0)
{
lean_del_object(v___x_1460_);
v___y_1421_ = v_a_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v___x_1462_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1458_;
}
}
else
{
v___y_1421_ = v_a_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
goto v___jp_1420_;
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v_a_1468_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1455_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1455_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
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
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v___x_1476_ = lean_box(0);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1476_);
v___x_1478_ = v___x_1450_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v_a_1481_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1447_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1447_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
v___jp_1409_:
{
lean_object* v___x_1418_; 
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1418_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_d_1415_, v___y_1417_, v___y_1412_, v___y_1410_, v___y_1414_, v___y_1411_, v___y_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref_known(v___x_1418_, 1);
v_e_1401_ = v_b_1416_;
v_a_1402_ = v___y_1417_;
v___y_1403_ = v___y_1412_;
v___y_1404_ = v___y_1410_;
v___y_1405_ = v___y_1414_;
v___y_1406_ = v___y_1411_;
v___y_1407_ = v___y_1413_;
goto _start;
}
else
{
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1418_;
}
}
v___jp_1420_:
{
switch(lean_obj_tag(v_e_1401_))
{
case 7:
{
lean_object* v_binderType_1427_; lean_object* v_body_1428_; 
v_binderType_1427_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_binderType_1427_);
v_body_1428_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_body_1428_);
lean_dec_ref_known(v_e_1401_, 3);
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1425_;
v___y_1412_ = v___y_1422_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1424_;
v_d_1415_ = v_binderType_1427_;
v_b_1416_ = v_body_1428_;
v___y_1417_ = v___y_1421_;
goto v___jp_1409_;
}
case 6:
{
lean_object* v_binderType_1429_; lean_object* v_body_1430_; 
v_binderType_1429_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_binderType_1429_);
v_body_1430_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_body_1430_);
lean_dec_ref_known(v_e_1401_, 3);
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1425_;
v___y_1412_ = v___y_1422_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1424_;
v_d_1415_ = v_binderType_1429_;
v_b_1416_ = v_body_1430_;
v___y_1417_ = v___y_1421_;
goto v___jp_1409_;
}
case 8:
{
lean_object* v_type_1431_; lean_object* v_value_1432_; lean_object* v_body_1433_; lean_object* v___x_1434_; 
v_type_1431_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_type_1431_);
v_value_1432_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_value_1432_);
v_body_1433_ = lean_ctor_get(v_e_1401_, 3);
lean_inc_ref(v_body_1433_);
lean_dec_ref_known(v_e_1401_, 4);
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_type_1431_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; 
lean_dec_ref_known(v___x_1434_, 1);
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1435_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_value_1432_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v_e_1401_ = v_body_1433_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
else
{
lean_dec_ref(v_body_1433_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1435_;
}
}
else
{
lean_dec_ref(v_body_1433_);
lean_dec_ref(v_value_1432_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1434_;
}
}
case 5:
{
lean_object* v_fn_1437_; lean_object* v_arg_1438_; lean_object* v___x_1439_; 
v_fn_1437_ = lean_ctor_get(v_e_1401_, 0);
lean_inc_ref(v_fn_1437_);
v_arg_1438_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_arg_1438_);
lean_dec_ref_known(v_e_1401_, 2);
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1439_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_fn_1437_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref_known(v___x_1439_, 1);
v_e_1401_ = v_arg_1438_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1438_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1439_;
}
}
case 10:
{
lean_object* v_expr_1441_; 
v_expr_1441_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_expr_1441_);
lean_dec_ref_known(v_e_1401_, 2);
v_e_1401_ = v_expr_1441_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
case 11:
{
lean_object* v_struct_1443_; 
v_struct_1443_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_struct_1443_);
lean_dec_ref_known(v_e_1401_, 3);
v_e_1401_ = v_struct_1443_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
default: 
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1489_, lean_object* v_f_1490_, lean_object* v_stopWhenVisited_1491_, lean_object* v_e_1492_, lean_object* v_a_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1500_; lean_object* v_res_1501_; 
v_stopWhenVisited_boxed_1500_ = lean_unbox(v_stopWhenVisited_1491_);
v_res_1501_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1489_, v_f_1490_, v_stopWhenVisited_boxed_1500_, v_e_1492_, v_a_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v_a_1493_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1502_, lean_object* v_f_1503_, lean_object* v_e_1504_, uint8_t v_stopWhenVisited_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = l_Lean_ForEachExprWhere_initCache;
v___x_1513_ = lean_st_mk_ref(v___x_1512_);
v___x_1514_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1502_, v_f_1503_, v_stopWhenVisited_1505_, v_e_1504_, v___x_1513_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1523_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_st_ref_get(v___x_1513_);
lean_dec(v___x_1513_);
lean_dec(v___x_1519_);
if (v_isShared_1518_ == 0)
{
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1515_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
else
{
lean_dec(v___x_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1524_, lean_object* v_f_1525_, lean_object* v_e_1526_, lean_object* v_stopWhenVisited_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1534_; lean_object* v_res_1535_; 
v_stopWhenVisited_boxed_1534_ = lean_unbox(v_stopWhenVisited_1527_);
v_res_1535_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1524_, v_f_1525_, v_e_1526_, v_stopWhenVisited_boxed_1534_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1537_, lean_object* v___f_1538_, uint8_t v___x_1539_, lean_object* v_e_1540_, lean_object* v_candidates_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1540_, v___y_1543_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___y_1552_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = l_Lean_Expr_hasFVar(v_a_1548_);
v___x_1550_ = lean_st_mk_ref(v_candidates_1541_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_a_1548_);
lean_dec_ref(v___f_1538_);
v___x_1562_ = lean_box(0);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___x_1550_);
v___x_1563_ = lean_apply_7(v___f_1537_, v___x_1562_, v___x_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
v___y_1552_ = v___x_1563_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1565_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1564_, v___f_1538_, v_a_1548_, v___x_1539_, v___x_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___x_1550_);
v___x_1567_ = lean_apply_7(v___f_1537_, v_a_1566_, v___x_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
v___y_1552_ = v___x_1567_;
goto v___jp_1551_;
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v___x_1550_);
lean_dec_ref(v___f_1537_);
v_a_1568_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1565_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1565_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
v___jp_1551_:
{
if (lean_obj_tag(v___y_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_a_1553_ = lean_ctor_get(v___y_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___y_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___y_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___y_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_st_ref_get(v___x_1550_);
lean_dec(v___x_1550_);
lean_dec(v___x_1557_);
if (v_isShared_1556_ == 0)
{
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1553_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_dec(v___x_1550_);
return v___y_1552_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v_candidates_1541_);
lean_dec_ref(v___f_1538_);
lean_dec_ref(v___f_1537_);
v_a_1576_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1547_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1547_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1584_, lean_object* v___f_1585_, lean_object* v___x_1586_, lean_object* v_e_1587_, lean_object* v_candidates_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_16881__boxed_1594_; lean_object* v_res_1595_; 
v___x_16881__boxed_1594_ = lean_unbox(v___x_1586_);
v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1584_, v___f_1585_, v___x_16881__boxed_1594_, v_e_1587_, v_candidates_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_____r_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_st_ref_get(v___y_1597_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_____r_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_e_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1620_ = lean_st_ref_take(v___y_1614_);
v___x_1621_ = lean_box(0);
v___x_1622_ = l_Lean_Expr_fvarId_x21(v_e_1613_);
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1620_, v___x_1622_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_st_ref_put(v___y_1614_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1621_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_e_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v_e_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
return v_x_1634_;
}
else
{
lean_object* v_key_1636_; lean_object* v_value_1637_; lean_object* v_tail_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1661_; 
v_key_1636_ = lean_ctor_get(v_x_1635_, 0);
v_value_1637_ = lean_ctor_get(v_x_1635_, 1);
v_tail_1638_ = lean_ctor_get(v_x_1635_, 2);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1635_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1640_ = v_x_1635_;
v_isShared_1641_ = v_isSharedCheck_1661_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_tail_1638_);
lean_inc(v_value_1637_);
lean_inc(v_key_1636_);
lean_dec(v_x_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1661_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; uint64_t v_fold_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; uint64_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1642_ = lean_array_get_size(v_x_1634_);
v___x_1643_ = l_Lean_instHashableFVarId_hash(v_key_1636_);
v___x_1644_ = 32ULL;
v___x_1645_ = lean_uint64_shift_right(v___x_1643_, v___x_1644_);
v_fold_1646_ = lean_uint64_xor(v___x_1643_, v___x_1645_);
v___x_1647_ = 16ULL;
v___x_1648_ = lean_uint64_shift_right(v_fold_1646_, v___x_1647_);
v___x_1649_ = lean_uint64_xor(v_fold_1646_, v___x_1648_);
v___x_1650_ = lean_uint64_to_usize(v___x_1649_);
v___x_1651_ = lean_usize_of_nat(v___x_1642_);
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_sub(v___x_1651_, v___x_1652_);
v___x_1654_ = lean_usize_land(v___x_1650_, v___x_1653_);
v___x_1655_ = lean_array_uget_borrowed(v_x_1634_, v___x_1654_);
lean_inc(v___x_1655_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 2, v___x_1655_);
v___x_1657_ = v___x_1640_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_key_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_value_1637_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_uset(v_x_1634_, v___x_1654_, v___x_1657_);
v_x_1634_ = v___x_1658_;
v_x_1635_ = v_tail_1638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1662_, lean_object* v_source_1663_, lean_object* v_target_1664_){
_start:
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = lean_array_get_size(v_source_1663_);
v___x_1666_ = lean_nat_dec_lt(v_i_1662_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_dec_ref(v_source_1663_);
lean_dec(v_i_1662_);
return v_target_1664_;
}
else
{
lean_object* v_es_1667_; lean_object* v___x_1668_; lean_object* v_source_1669_; lean_object* v_target_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_es_1667_ = lean_array_fget(v_source_1663_, v_i_1662_);
v___x_1668_ = lean_box(0);
v_source_1669_ = lean_array_fset(v_source_1663_, v_i_1662_, v___x_1668_);
v_target_1670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1664_, v_es_1667_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_add(v_i_1662_, v___x_1671_);
lean_dec(v_i_1662_);
v_i_1662_ = v___x_1672_;
v_source_1663_ = v_source_1669_;
v_target_1664_ = v_target_1670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_nbuckets_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1675_ = lean_array_get_size(v_data_1674_);
v___x_1676_ = lean_unsigned_to_nat(2u);
v_nbuckets_1677_ = lean_nat_mul(v___x_1675_, v___x_1676_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_mk_array(v_nbuckets_1677_, v___x_1679_);
v___x_1681_ = lean_array_propagate_mark(v_data_1674_, v___x_1680_);
v___x_1682_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1678_, v_data_1674_, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1683_, lean_object* v_a_1684_, lean_object* v_b_1685_){
_start:
{
lean_object* v_size_1686_; lean_object* v_buckets_1687_; lean_object* v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v_fold_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; lean_object* v_bkt_1701_; uint8_t v___x_1702_; 
v_size_1686_ = lean_ctor_get(v_m_1683_, 0);
v_buckets_1687_ = lean_ctor_get(v_m_1683_, 1);
v___x_1688_ = lean_array_get_size(v_buckets_1687_);
v___x_1689_ = l_Lean_instHashableFVarId_hash(v_a_1684_);
v___x_1690_ = 32ULL;
v___x_1691_ = lean_uint64_shift_right(v___x_1689_, v___x_1690_);
v_fold_1692_ = lean_uint64_xor(v___x_1689_, v___x_1691_);
v___x_1693_ = 16ULL;
v___x_1694_ = lean_uint64_shift_right(v_fold_1692_, v___x_1693_);
v___x_1695_ = lean_uint64_xor(v_fold_1692_, v___x_1694_);
v___x_1696_ = lean_uint64_to_usize(v___x_1695_);
v___x_1697_ = lean_usize_of_nat(v___x_1688_);
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_sub(v___x_1697_, v___x_1698_);
v___x_1700_ = lean_usize_land(v___x_1696_, v___x_1699_);
v_bkt_1701_ = lean_array_uget_borrowed(v_buckets_1687_, v___x_1700_);
v___x_1702_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1684_, v_bkt_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1723_; 
lean_inc_ref(v_buckets_1687_);
lean_inc(v_size_1686_);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_m_1683_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; lean_object* v_unused_1725_; 
v_unused_1724_ = lean_ctor_get(v_m_1683_, 1);
lean_dec(v_unused_1724_);
v_unused_1725_ = lean_ctor_get(v_m_1683_, 0);
lean_dec(v_unused_1725_);
v___x_1704_ = v_m_1683_;
v_isShared_1705_ = v_isSharedCheck_1723_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v_m_1683_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1723_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v_size_x27_1707_; lean_object* v___x_1708_; lean_object* v_buckets_x27_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1706_ = lean_unsigned_to_nat(1u);
v_size_x27_1707_ = lean_nat_add(v_size_1686_, v___x_1706_);
lean_dec(v_size_1686_);
lean_inc(v_bkt_1701_);
v___x_1708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1708_, 0, v_a_1684_);
lean_ctor_set(v___x_1708_, 1, v_b_1685_);
lean_ctor_set(v___x_1708_, 2, v_bkt_1701_);
v_buckets_x27_1709_ = lean_array_uset(v_buckets_1687_, v___x_1700_, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(4u);
v___x_1711_ = lean_nat_mul(v_size_x27_1707_, v___x_1710_);
v___x_1712_ = lean_unsigned_to_nat(3u);
v___x_1713_ = lean_nat_div(v___x_1711_, v___x_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_array_get_size(v_buckets_x27_1709_);
v___x_1715_ = lean_nat_dec_le(v___x_1713_, v___x_1714_);
lean_dec(v___x_1713_);
if (v___x_1715_ == 0)
{
lean_object* v_val_1716_; lean_object* v___x_1718_; 
v_val_1716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1709_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_val_1716_);
lean_ctor_set(v___x_1704_, 0, v_size_x27_1707_);
v___x_1718_ = v___x_1704_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_size_x27_1707_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_val_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v___x_1721_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_buckets_x27_1709_);
lean_ctor_set(v___x_1704_, 0, v_size_x27_1707_);
v___x_1721_ = v___x_1704_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_size_x27_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_buckets_x27_1709_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_dec(v_b_1685_);
lean_dec(v_a_1684_);
return v_m_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1728_, size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_b_1731_);
return v___x_1738_;
}
else
{
lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1801_; 
v_snd_1739_ = lean_ctor_get(v_b_1731_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_b_1731_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_b_1731_, 0);
lean_dec(v_unused_1802_);
v___x_1741_ = v_b_1731_;
v_isShared_1742_ = v_isSharedCheck_1801_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_dec(v_b_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1801_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v_a_1745_; lean_object* v_a_1752_; 
v___x_1743_ = lean_box(0);
v_a_1752_ = lean_array_uget_borrowed(v_as_1728_, v_i_1730_);
if (lean_obj_tag(v_a_1752_) == 0)
{
v_a_1745_ = v_snd_1739_;
goto v___jp_1744_;
}
else
{
lean_object* v_val_1753_; uint8_t v___x_1754_; 
v_val_1753_ = lean_ctor_get(v_a_1752_, 0);
v___x_1754_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v_candidates_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___x_1779_; 
v___f_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1757_ = l_Lean_LocalDecl_type(v_val_1753_);
lean_inc_ref(v___x_1757_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1755_, v___f_1756_, v___x_1754_, v___x_1757_, v_snd_1739_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = l_Lean_LocalDecl_value_x3f(v_val_1753_, v___x_1754_);
if (lean_obj_tag(v___x_1781_) == 0)
{
v_candidates_1759_ = v_a_1780_;
v___y_1760_ = v___y_1732_;
v___y_1761_ = v___y_1733_;
v___y_1762_ = v___y_1734_;
v___y_1763_ = v___y_1735_;
goto v___jp_1758_;
}
else
{
lean_object* v_val_1782_; lean_object* v___x_1783_; 
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1755_, v___f_1756_, v___x_1754_, v_val_1782_, v_a_1780_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v_candidates_1759_ = v_a_1784_;
v___y_1760_ = v___y_1732_;
v___y_1761_ = v___y_1733_;
v___y_1762_ = v___y_1734_;
v___y_1763_ = v___y_1735_;
goto v___jp_1758_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___x_1757_);
lean_del_object(v___x_1741_);
v_a_1785_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1783_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v___x_1757_);
lean_del_object(v___x_1741_);
v_a_1793_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1779_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1779_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
v___jp_1758_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_isProp(v___x_1757_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; uint8_t v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_unbox(v_a_1765_);
lean_dec(v_a_1765_);
if (v___x_1766_ == 0)
{
v_a_1745_ = v_candidates_1759_;
goto v___jp_1744_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = l_Lean_LocalDecl_hasValue(v_val_1753_, v___x_1754_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = l_Lean_LocalDecl_fvarId(v_val_1753_);
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1759_, v___x_1768_, v___x_1769_);
v_a_1745_ = v___x_1770_;
goto v___jp_1744_;
}
else
{
v_a_1745_ = v_candidates_1759_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_candidates_1759_);
lean_del_object(v___x_1741_);
v_a_1771_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1764_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1764_);
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
else
{
v_a_1745_ = v_snd_1739_;
goto v___jp_1744_;
}
}
v___jp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 1, v_a_1745_);
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1747_ = v___x_1741_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1745_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
size_t v___x_1748_; size_t v___x_1749_; 
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_i_1730_, v___x_1748_);
v_i_1730_ = v___x_1749_;
v_b_1731_ = v___x_1747_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1803_, lean_object* v_sz_1804_, lean_object* v_i_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
size_t v_sz_boxed_1812_; size_t v_i_boxed_1813_; lean_object* v_res_1814_; 
v_sz_boxed_1812_ = lean_unbox_usize(v_sz_1804_);
lean_dec(v_sz_1804_);
v_i_boxed_1813_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1803_, v_sz_boxed_1812_, v_i_boxed_1813_, v_b_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_as_1803_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1815_, size_t v_sz_1816_, size_t v_i_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_lt(v_i_1817_, v_sz_1816_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1818_);
return v___x_1825_;
}
else
{
lean_object* v_snd_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1888_; 
v_snd_1826_ = lean_ctor_get(v_b_1818_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_b_1818_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v_b_1818_, 0);
lean_dec(v_unused_1889_);
v___x_1828_ = v_b_1818_;
v_isShared_1829_ = v_isSharedCheck_1888_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_snd_1826_);
lean_dec(v_b_1818_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1888_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v_a_1832_; lean_object* v_a_1839_; 
v___x_1830_ = lean_box(0);
v_a_1839_ = lean_array_uget_borrowed(v_as_1815_, v_i_1817_);
if (lean_obj_tag(v_a_1839_) == 0)
{
v_a_1832_ = v_snd_1826_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1840_; uint8_t v___x_1841_; 
v_val_1840_ = lean_ctor_get(v_a_1839_, 0);
v___x_1841_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___f_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v_candidates_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___x_1866_; 
v___f_1842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1844_ = l_Lean_LocalDecl_type(v_val_1840_);
lean_inc_ref(v___x_1844_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1842_, v___f_1843_, v___x_1841_, v___x_1844_, v_snd_1826_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = l_Lean_LocalDecl_value_x3f(v_val_1840_, v___x_1841_);
if (lean_obj_tag(v___x_1868_) == 0)
{
v_candidates_1846_ = v_a_1867_;
v___y_1847_ = v___y_1819_;
v___y_1848_ = v___y_1820_;
v___y_1849_ = v___y_1821_;
v___y_1850_ = v___y_1822_;
goto v___jp_1845_;
}
else
{
lean_object* v_val_1869_; lean_object* v___x_1870_; 
v_val_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1842_, v___f_1843_, v___x_1841_, v_val_1869_, v_a_1867_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v_candidates_1846_ = v_a_1871_;
v___y_1847_ = v___y_1819_;
v___y_1848_ = v___y_1820_;
v___y_1849_ = v___y_1821_;
v___y_1850_ = v___y_1822_;
goto v___jp_1845_;
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___x_1844_);
lean_del_object(v___x_1828_);
v_a_1872_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1870_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v___x_1844_);
lean_del_object(v___x_1828_);
v_a_1880_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1866_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1866_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
v___jp_1845_:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_Meta_isProp(v___x_1844_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; uint8_t v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v___x_1853_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
if (v___x_1853_ == 0)
{
v_a_1832_ = v_candidates_1846_;
goto v___jp_1831_;
}
else
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Lean_LocalDecl_hasValue(v_val_1840_, v___x_1841_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = l_Lean_LocalDecl_fvarId(v_val_1840_);
v___x_1856_ = lean_box(0);
v___x_1857_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1846_, v___x_1855_, v___x_1856_);
v_a_1832_ = v___x_1857_;
goto v___jp_1831_;
}
else
{
v_a_1832_ = v_candidates_1846_;
goto v___jp_1831_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_candidates_1846_);
lean_del_object(v___x_1828_);
v_a_1858_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1851_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1851_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
else
{
v_a_1832_ = v_snd_1826_;
goto v___jp_1831_;
}
}
v___jp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v_a_1832_);
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1834_ = v___x_1828_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_a_1832_);
v___x_1834_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_i_1817_, v___x_1835_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1815_, v_sz_1816_, v___x_1836_, v___x_1834_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
return v___x_1837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1890_, lean_object* v_sz_1891_, lean_object* v_i_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
size_t v_sz_boxed_1899_; size_t v_i_boxed_1900_; lean_object* v_res_1901_; 
v_sz_boxed_1899_ = lean_unbox_usize(v_sz_1891_);
lean_dec(v_sz_1891_);
v_i_boxed_1900_ = lean_unbox_usize(v_i_1892_);
lean_dec(v_i_1892_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1890_, v_sz_boxed_1899_, v_i_boxed_1900_, v_b_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v_as_1890_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1902_, size_t v_sz_1903_, size_t v_i_1904_, lean_object* v_b_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
uint8_t v___x_1911_; 
v___x_1911_ = lean_usize_dec_lt(v_i_1904_, v_sz_1903_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_b_1905_);
return v___x_1912_;
}
else
{
lean_object* v_snd_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1975_; 
v_snd_1913_ = lean_ctor_get(v_b_1905_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_b_1905_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_b_1905_, 0);
lean_dec(v_unused_1976_);
v___x_1915_ = v_b_1905_;
v_isShared_1916_ = v_isSharedCheck_1975_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snd_1913_);
lean_dec(v_b_1905_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1975_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v_a_1919_; lean_object* v_a_1926_; 
v___x_1917_ = lean_box(0);
v_a_1926_ = lean_array_uget_borrowed(v_as_1902_, v_i_1904_);
if (lean_obj_tag(v_a_1926_) == 0)
{
v_a_1919_ = v_snd_1913_;
goto v___jp_1918_;
}
else
{
lean_object* v_val_1927_; uint8_t v___x_1928_; 
v_val_1927_ = lean_ctor_get(v_a_1926_, 0);
v___x_1928_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; lean_object* v_candidates_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___x_1953_; 
v___f_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1931_ = l_Lean_LocalDecl_type(v_val_1927_);
lean_inc_ref(v___x_1931_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1929_, v___f_1930_, v___x_1928_, v___x_1931_, v_snd_1913_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = l_Lean_LocalDecl_value_x3f(v_val_1927_, v___x_1928_);
if (lean_obj_tag(v___x_1955_) == 0)
{
v_candidates_1933_ = v_a_1954_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
v___y_1937_ = v___y_1909_;
goto v___jp_1932_;
}
else
{
lean_object* v_val_1956_; lean_object* v___x_1957_; 
v_val_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_val_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1929_, v___f_1930_, v___x_1928_, v_val_1956_, v_a_1954_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_candidates_1933_ = v_a_1958_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
v___y_1937_ = v___y_1909_;
goto v___jp_1932_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v___x_1931_);
lean_del_object(v___x_1915_);
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
lean_dec_ref(v___x_1931_);
lean_del_object(v___x_1915_);
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
v___jp_1932_:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_Meta_isProp(v___x_1931_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
if (v___x_1940_ == 0)
{
v_a_1919_ = v_candidates_1933_;
goto v___jp_1918_;
}
else
{
uint8_t v___x_1941_; 
v___x_1941_ = l_Lean_LocalDecl_hasValue(v_val_1927_, v___x_1928_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = l_Lean_LocalDecl_fvarId(v_val_1927_);
v___x_1943_ = lean_box(0);
v___x_1944_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1933_, v___x_1942_, v___x_1943_);
v_a_1919_ = v___x_1944_;
goto v___jp_1918_;
}
else
{
v_a_1919_ = v_candidates_1933_;
goto v___jp_1918_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_candidates_1933_);
lean_del_object(v___x_1915_);
v_a_1945_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1938_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1938_);
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
v_a_1919_ = v_snd_1913_;
goto v___jp_1918_;
}
}
v___jp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_a_1919_);
lean_ctor_set(v___x_1915_, 0, v___x_1917_);
v___x_1921_ = v___x_1915_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1919_);
v___x_1921_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
size_t v___x_1922_; size_t v___x_1923_; 
v___x_1922_ = ((size_t)1ULL);
v___x_1923_ = lean_usize_add(v_i_1904_, v___x_1922_);
v_i_1904_ = v___x_1923_;
v_b_1905_ = v___x_1921_;
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
lean_object* v_snd_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2062_; 
v_snd_2000_ = lean_ctor_get(v_b_1992_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_b_1992_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v_b_1992_, 0);
lean_dec(v_unused_2063_);
v___x_2002_ = v_b_1992_;
v_isShared_2003_ = v_isSharedCheck_2062_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_2000_);
lean_dec(v_b_1992_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2062_;
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
lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v_candidates_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___x_2040_; 
v___f_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2018_ = l_Lean_LocalDecl_type(v_val_2014_);
lean_inc_ref(v___x_2018_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2016_, v___f_2017_, v___x_2015_, v___x_2018_, v_snd_2000_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = l_Lean_LocalDecl_value_x3f(v_val_2014_, v___x_2015_);
if (lean_obj_tag(v___x_2042_) == 0)
{
v_candidates_2020_ = v_a_2041_;
v___y_2021_ = v___y_1993_;
v___y_2022_ = v___y_1994_;
v___y_2023_ = v___y_1995_;
v___y_2024_ = v___y_1996_;
goto v___jp_2019_;
}
else
{
lean_object* v_val_2043_; lean_object* v___x_2044_; 
v_val_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_val_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2016_, v___f_2017_, v___x_2015_, v_val_2043_, v_a_2041_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v_candidates_2020_ = v_a_2045_;
v___y_2021_ = v___y_1993_;
v___y_2022_ = v___y_1994_;
v___y_2023_ = v___y_1995_;
v___y_2024_ = v___y_1996_;
goto v___jp_2019_;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec_ref(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2046_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2044_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2044_);
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
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v___x_2018_);
lean_del_object(v___x_2002_);
v_a_2054_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2040_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2040_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
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
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_LocalDecl_hasValue(v_val_2014_, v___x_2015_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_LocalDecl_fvarId(v_val_2014_);
v___x_2030_ = lean_box(0);
v___x_2031_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_2020_, v___x_2029_, v___x_2030_);
v_a_2006_ = v___x_2031_;
goto v___jp_2005_;
}
else
{
v_a_2006_ = v_candidates_2020_;
goto v___jp_2005_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_candidates_2020_);
lean_del_object(v___x_2002_);
v_a_2032_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2025_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2025_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2064_, lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_b_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
size_t v_sz_boxed_2073_; size_t v_i_boxed_2074_; lean_object* v_res_2075_; 
v_sz_boxed_2073_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2074_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2064_, v_sz_boxed_2073_, v_i_boxed_2074_, v_b_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec_ref(v_as_2064_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2076_, lean_object* v_n_2077_, lean_object* v_b_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
if (lean_obj_tag(v_n_2077_) == 0)
{
lean_object* v_cs_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v_cs_2084_ = lean_ctor_get(v_n_2077_, 0);
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_b_2078_);
v_sz_2087_ = lean_array_size(v_cs_2084_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2076_, v_cs_2084_, v_sz_2087_, v___x_2088_, v___x_2086_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_fst_2094_; 
v_fst_2094_ = lean_ctor_get(v_a_2090_, 0);
if (lean_obj_tag(v_fst_2094_) == 0)
{
lean_object* v_snd_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v_snd_2095_ = lean_ctor_get(v_a_2090_, 1);
lean_inc(v_snd_2095_);
lean_dec(v_a_2090_);
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_snd_2095_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2096_);
v___x_2098_ = v___x_2092_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2102_; 
lean_inc_ref(v_fst_2094_);
lean_dec(v_a_2090_);
v_val_2100_ = lean_ctor_get(v_fst_2094_, 0);
lean_inc(v_val_2100_);
lean_dec_ref_known(v_fst_2094_, 1);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_val_2100_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_val_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2089_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2089_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_vs_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v_vs_2113_ = lean_ctor_get(v_n_2077_, 0);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v_b_2078_);
v_sz_2116_ = lean_array_size(v_vs_2113_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2113_, v_sz_2116_, v___x_2117_, v___x_2115_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2133_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2133_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2133_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_fst_2123_; 
v_fst_2123_ = lean_ctor_get(v_a_2119_, 0);
if (lean_obj_tag(v_fst_2123_) == 0)
{
lean_object* v_snd_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_snd_2124_ = lean_ctor_get(v_a_2119_, 1);
lean_inc(v_snd_2124_);
lean_dec(v_a_2119_);
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_snd_2124_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2125_);
v___x_2127_ = v___x_2121_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2131_; 
lean_inc_ref(v_fst_2123_);
lean_dec(v_a_2119_);
v_val_2129_ = lean_ctor_get(v_fst_2123_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v_fst_2123_, 1);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v_val_2129_);
v___x_2131_ = v___x_2121_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_val_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2118_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2118_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2142_, lean_object* v_as_2143_, size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2145_, v_sz_2144_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_b_2146_);
return v___x_2153_;
}
else
{
lean_object* v_snd_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2188_; 
v_snd_2154_ = lean_ctor_get(v_b_2146_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_b_2146_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v_b_2146_, 0);
lean_dec(v_unused_2189_);
v___x_2156_ = v_b_2146_;
v_isShared_2157_ = v_isSharedCheck_2188_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_snd_2154_);
lean_dec(v_b_2146_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2188_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v_a_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_box(0);
v_a_2159_ = lean_array_uget_borrowed(v_as_2143_, v_i_2145_);
lean_inc(v_snd_2154_);
v___x_2160_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2142_, v_a_2159_, v_snd_2154_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2179_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2179_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2179_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2161_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2165_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2154_);
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
lean_object* v_a_2172_; lean_object* v___x_2174_; 
lean_del_object(v___x_2163_);
lean_dec(v_snd_2154_);
v_a_2172_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v_a_2161_, 1);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v_a_2172_);
lean_ctor_set(v___x_2156_, 0, v___x_2158_);
v___x_2174_ = v___x_2156_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2172_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
size_t v___x_2175_; size_t v___x_2176_; 
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = lean_usize_add(v_i_2145_, v___x_2175_);
v_i_2145_ = v___x_2176_;
v_b_2146_ = v___x_2174_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2156_);
lean_dec(v_snd_2154_);
v_a_2180_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2160_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2160_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2190_, lean_object* v_as_2191_, lean_object* v_sz_2192_, lean_object* v_i_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2192_);
lean_dec(v_sz_2192_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2193_);
lean_dec(v_i_2193_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2190_, v_as_2191_, v_sz_boxed_2200_, v_i_boxed_2201_, v_b_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v_as_2191_);
lean_dec_ref(v_init_2190_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2203_, lean_object* v_n_2204_, lean_object* v_b_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2203_, v_n_2204_, v_b_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec_ref(v_n_2204_);
lean_dec_ref(v_init_2203_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2212_, lean_object* v_init_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_root_2219_; lean_object* v_tail_2220_; lean_object* v___x_2221_; 
v_root_2219_ = lean_ctor_get(v_t_2212_, 0);
v_tail_2220_ = lean_ctor_get(v_t_2212_, 1);
lean_inc_ref(v_init_2213_);
v___x_2221_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2213_, v_root_2219_, v_init_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec_ref(v_init_2213_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2258_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2258_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2258_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
if (lean_obj_tag(v_a_2222_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; 
v_a_2226_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v_a_2222_, 1);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_a_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_2235_; 
lean_del_object(v___x_2224_);
v_a_2230_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v_a_2222_, 1);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_a_2230_);
v_sz_2233_ = lean_array_size(v_tail_2220_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2220_, v_sz_2233_, v___x_2234_, v___x_2232_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2249_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2249_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2249_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_fst_2240_; 
v_fst_2240_ = lean_ctor_get(v_a_2236_, 0);
if (lean_obj_tag(v_fst_2240_) == 0)
{
lean_object* v_snd_2241_; lean_object* v___x_2243_; 
v_snd_2241_ = lean_ctor_get(v_a_2236_, 1);
lean_inc(v_snd_2241_);
lean_dec(v_a_2236_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_snd_2241_);
v___x_2243_ = v___x_2238_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_snd_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
else
{
lean_object* v_val_2245_; lean_object* v___x_2247_; 
lean_inc_ref(v_fst_2240_);
lean_dec(v_a_2236_);
v_val_2245_ = lean_ctor_get(v_fst_2240_, 0);
lean_inc(v_val_2245_);
lean_dec_ref_known(v_fst_2240_, 1);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_val_2245_);
v___x_2247_ = v___x_2238_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_val_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2235_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2235_);
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
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2221_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2221_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2267_, lean_object* v_init_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2267_, v_init_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_t_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v_buckets_2277_; lean_object* v___x_2278_; uint64_t v___x_2279_; uint64_t v___x_2280_; uint64_t v___x_2281_; uint64_t v_fold_2282_; uint64_t v___x_2283_; uint64_t v___x_2284_; uint64_t v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; size_t v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_buckets_2277_ = lean_ctor_get(v_m_2275_, 1);
v___x_2278_ = lean_array_get_size(v_buckets_2277_);
v___x_2279_ = l_Lean_instHashableFVarId_hash(v_a_2276_);
v___x_2280_ = 32ULL;
v___x_2281_ = lean_uint64_shift_right(v___x_2279_, v___x_2280_);
v_fold_2282_ = lean_uint64_xor(v___x_2279_, v___x_2281_);
v___x_2283_ = 16ULL;
v___x_2284_ = lean_uint64_shift_right(v_fold_2282_, v___x_2283_);
v___x_2285_ = lean_uint64_xor(v_fold_2282_, v___x_2284_);
v___x_2286_ = lean_uint64_to_usize(v___x_2285_);
v___x_2287_ = lean_usize_of_nat(v___x_2278_);
v___x_2288_ = ((size_t)1ULL);
v___x_2289_ = lean_usize_sub(v___x_2287_, v___x_2288_);
v___x_2290_ = lean_usize_land(v___x_2286_, v___x_2289_);
v___x_2291_ = lean_array_uget_borrowed(v_buckets_2277_, v___x_2290_);
v___x_2292_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2276_, v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2293_, lean_object* v_a_2294_){
_start:
{
uint8_t v_res_2295_; lean_object* v_r_2296_; 
v_res_2295_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2293_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v_m_2293_);
v_r_2296_ = lean_box(v_res_2295_);
return v_r_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2297_, lean_object* v_as_2298_, size_t v_sz_2299_, size_t v_i_2300_, lean_object* v_b_2301_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_lt(v_i_2300_, v_sz_2299_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_b_2301_);
return v___x_2304_;
}
else
{
lean_object* v_snd_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2323_; 
v_snd_2305_ = lean_ctor_get(v_b_2301_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_b_2301_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v_b_2301_, 0);
lean_dec(v_unused_2324_);
v___x_2307_ = v_b_2301_;
v_isShared_2308_ = v_isSharedCheck_2323_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_snd_2305_);
lean_dec(v_b_2301_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2323_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v_a_2311_; lean_object* v_a_2318_; 
v___x_2309_ = lean_box(0);
v_a_2318_ = lean_array_uget_borrowed(v_as_2298_, v_i_2300_);
if (lean_obj_tag(v_a_2318_) == 0)
{
v_a_2311_ = v_snd_2305_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_val_2319_ = lean_ctor_get(v_a_2318_, 0);
v___x_2320_ = l_Lean_LocalDecl_fvarId(v_val_2319_);
v___x_2321_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2297_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_dec(v___x_2320_);
v_a_2311_ = v_snd_2305_;
goto v___jp_2310_;
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_array_push(v_snd_2305_, v___x_2320_);
v_a_2311_ = v___x_2322_;
goto v___jp_2310_;
}
}
v___jp_2310_:
{
lean_object* v___x_2313_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v_a_2311_);
lean_ctor_set(v___x_2307_, 0, v___x_2309_);
v___x_2313_ = v___x_2307_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_a_2311_);
v___x_2313_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
size_t v___x_2314_; size_t v___x_2315_; 
v___x_2314_ = ((size_t)1ULL);
v___x_2315_ = lean_usize_add(v_i_2300_, v___x_2314_);
v_i_2300_ = v___x_2315_;
v_b_2301_ = v___x_2313_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2325_, lean_object* v_as_2326_, lean_object* v_sz_2327_, lean_object* v_i_2328_, lean_object* v_b_2329_, lean_object* v___y_2330_){
_start:
{
size_t v_sz_boxed_2331_; size_t v_i_boxed_2332_; lean_object* v_res_2333_; 
v_sz_boxed_2331_ = lean_unbox_usize(v_sz_2327_);
lean_dec(v_sz_2327_);
v_i_boxed_2332_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2325_, v_as_2326_, v_sz_boxed_2331_, v_i_boxed_2332_, v_b_2329_);
lean_dec_ref(v_as_2326_);
lean_dec_ref(v_a_2325_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2334_, lean_object* v_as_2335_, size_t v_sz_2336_, size_t v_i_2337_, lean_object* v_b_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_usize_dec_lt(v_i_2337_, v_sz_2336_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_b_2338_);
return v___x_2345_;
}
else
{
lean_object* v_snd_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2364_; 
v_snd_2346_ = lean_ctor_get(v_b_2338_, 1);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_b_2338_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v_b_2338_, 0);
lean_dec(v_unused_2365_);
v___x_2348_ = v_b_2338_;
v_isShared_2349_ = v_isSharedCheck_2364_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_snd_2346_);
lean_dec(v_b_2338_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2364_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v_a_2352_; lean_object* v_a_2359_; 
v___x_2350_ = lean_box(0);
v_a_2359_ = lean_array_uget_borrowed(v_as_2335_, v_i_2337_);
if (lean_obj_tag(v_a_2359_) == 0)
{
v_a_2352_ = v_snd_2346_;
goto v___jp_2351_;
}
else
{
lean_object* v_val_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_val_2360_ = lean_ctor_get(v_a_2359_, 0);
v___x_2361_ = l_Lean_LocalDecl_fvarId(v_val_2360_);
v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2334_, v___x_2361_);
if (v___x_2362_ == 0)
{
lean_dec(v___x_2361_);
v_a_2352_ = v_snd_2346_;
goto v___jp_2351_;
}
else
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_array_push(v_snd_2346_, v___x_2361_);
v_a_2352_ = v___x_2363_;
goto v___jp_2351_;
}
}
v___jp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 1, v_a_2352_);
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2354_ = v___x_2348_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_a_2352_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
size_t v___x_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2337_, v___x_2355_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2334_, v_as_2335_, v_sz_2336_, v___x_2356_, v___x_2354_);
return v___x_2357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2366_, lean_object* v_as_2367_, lean_object* v_sz_2368_, lean_object* v_i_2369_, lean_object* v_b_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
size_t v_sz_boxed_2376_; size_t v_i_boxed_2377_; lean_object* v_res_2378_; 
v_sz_boxed_2376_ = lean_unbox_usize(v_sz_2368_);
lean_dec(v_sz_2368_);
v_i_boxed_2377_ = lean_unbox_usize(v_i_2369_);
lean_dec(v_i_2369_);
v_res_2378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2366_, v_as_2367_, v_sz_boxed_2376_, v_i_boxed_2377_, v_b_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_as_2367_);
lean_dec_ref(v_a_2366_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2379_, lean_object* v_a_2380_, lean_object* v_n_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
if (lean_obj_tag(v_n_2381_) == 0)
{
lean_object* v_cs_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v_cs_2388_ = lean_ctor_get(v_n_2381_, 0);
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v_b_2382_);
v_sz_2391_ = lean_array_size(v_cs_2388_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2379_, v_a_2380_, v_cs_2388_, v_sz_2391_, v___x_2392_, v___x_2390_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2408_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2408_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2408_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_fst_2398_; 
v_fst_2398_ = lean_ctor_get(v_a_2394_, 0);
if (lean_obj_tag(v_fst_2398_) == 0)
{
lean_object* v_snd_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v_snd_2399_ = lean_ctor_get(v_a_2394_, 1);
lean_inc(v_snd_2399_);
lean_dec(v_a_2394_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_snd_2399_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2400_);
v___x_2402_ = v___x_2396_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
else
{
lean_object* v_val_2404_; lean_object* v___x_2406_; 
lean_inc_ref(v_fst_2398_);
lean_dec(v_a_2394_);
v_val_2404_ = lean_ctor_get(v_fst_2398_, 0);
lean_inc(v_val_2404_);
lean_dec_ref_known(v_fst_2398_, 1);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v_val_2404_);
v___x_2406_ = v___x_2396_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_val_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2393_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2393_);
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
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_vs_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
v_vs_2417_ = lean_ctor_get(v_n_2381_, 0);
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_b_2382_);
v_sz_2420_ = lean_array_size(v_vs_2417_);
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2380_, v_vs_2417_, v_sz_2420_, v___x_2421_, v___x_2419_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2437_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2437_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2437_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_fst_2427_; 
v_fst_2427_ = lean_ctor_get(v_a_2423_, 0);
if (lean_obj_tag(v_fst_2427_) == 0)
{
lean_object* v_snd_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v_snd_2428_ = lean_ctor_get(v_a_2423_, 1);
lean_inc(v_snd_2428_);
lean_dec(v_a_2423_);
v___x_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_snd_2428_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2429_);
v___x_2431_ = v___x_2425_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
else
{
lean_object* v_val_2433_; lean_object* v___x_2435_; 
lean_inc_ref(v_fst_2427_);
lean_dec(v_a_2423_);
v_val_2433_ = lean_ctor_get(v_fst_2427_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v_fst_2427_, 1);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v_val_2433_);
v___x_2435_ = v___x_2425_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_val_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_a_2438_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2422_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2422_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2446_, lean_object* v_a_2447_, lean_object* v_as_2448_, size_t v_sz_2449_, size_t v_i_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
uint8_t v___x_2457_; 
v___x_2457_ = lean_usize_dec_lt(v_i_2450_, v_sz_2449_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_b_2451_);
return v___x_2458_;
}
else
{
lean_object* v_snd_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2493_; 
v_snd_2459_ = lean_ctor_get(v_b_2451_, 1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_b_2451_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_b_2451_, 0);
lean_dec(v_unused_2494_);
v___x_2461_ = v_b_2451_;
v_isShared_2462_ = v_isSharedCheck_2493_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_snd_2459_);
lean_dec(v_b_2451_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2493_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v_a_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_box(0);
v_a_2464_ = lean_array_uget_borrowed(v_as_2448_, v_i_2450_);
lean_inc(v_snd_2459_);
v___x_2465_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2446_, v_a_2447_, v_a_2464_, v_snd_2459_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2484_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2484_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2484_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
if (lean_obj_tag(v_a_2466_) == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2466_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2470_);
v___x_2472_ = v___x_2461_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_snd_2459_);
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
lean_object* v_a_2477_; lean_object* v___x_2479_; 
lean_del_object(v___x_2468_);
lean_dec(v_snd_2459_);
v_a_2477_ = lean_ctor_get(v_a_2466_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v_a_2466_, 1);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v_a_2477_);
lean_ctor_set(v___x_2461_, 0, v___x_2463_);
v___x_2479_ = v___x_2461_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_a_2477_);
v___x_2479_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
size_t v___x_2480_; size_t v___x_2481_; 
v___x_2480_ = ((size_t)1ULL);
v___x_2481_ = lean_usize_add(v_i_2450_, v___x_2480_);
v_i_2450_ = v___x_2481_;
v_b_2451_ = v___x_2479_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_del_object(v___x_2461_);
lean_dec(v_snd_2459_);
v_a_2485_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2465_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2465_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2495_, lean_object* v_a_2496_, lean_object* v_as_2497_, lean_object* v_sz_2498_, lean_object* v_i_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2498_);
lean_dec(v_sz_2498_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2495_, v_a_2496_, v_as_2497_, v_sz_boxed_2506_, v_i_boxed_2507_, v_b_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_as_2497_);
lean_dec_ref(v_a_2496_);
lean_dec_ref(v_init_2495_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2509_, lean_object* v_a_2510_, lean_object* v_n_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2509_, v_a_2510_, v_n_2511_, v_b_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v_n_2511_);
lean_dec_ref(v_a_2510_);
lean_dec_ref(v_init_2509_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2519_, lean_object* v_as_2520_, size_t v_sz_2521_, size_t v_i_2522_, lean_object* v_b_2523_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_lt(v_i_2522_, v_sz_2521_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_b_2523_);
return v___x_2526_;
}
else
{
lean_object* v_snd_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2545_; 
v_snd_2527_ = lean_ctor_get(v_b_2523_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_b_2523_);
if (v_isSharedCheck_2545_ == 0)
{
lean_object* v_unused_2546_; 
v_unused_2546_ = lean_ctor_get(v_b_2523_, 0);
lean_dec(v_unused_2546_);
v___x_2529_ = v_b_2523_;
v_isShared_2530_ = v_isSharedCheck_2545_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_snd_2527_);
lean_dec(v_b_2523_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2545_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v_a_2533_; lean_object* v_a_2540_; 
v___x_2531_ = lean_box(0);
v_a_2540_ = lean_array_uget_borrowed(v_as_2520_, v_i_2522_);
if (lean_obj_tag(v_a_2540_) == 0)
{
v_a_2533_ = v_snd_2527_;
goto v___jp_2532_;
}
else
{
lean_object* v_val_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_val_2541_ = lean_ctor_get(v_a_2540_, 0);
v___x_2542_ = l_Lean_LocalDecl_fvarId(v_val_2541_);
v___x_2543_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2519_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_dec(v___x_2542_);
v_a_2533_ = v_snd_2527_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_array_push(v_snd_2527_, v___x_2542_);
v_a_2533_ = v___x_2544_;
goto v___jp_2532_;
}
}
v___jp_2532_:
{
lean_object* v___x_2535_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v_a_2533_);
lean_ctor_set(v___x_2529_, 0, v___x_2531_);
v___x_2535_ = v___x_2529_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_a_2533_);
v___x_2535_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
size_t v___x_2536_; size_t v___x_2537_; 
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_add(v_i_2522_, v___x_2536_);
v_i_2522_ = v___x_2537_;
v_b_2523_ = v___x_2535_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2547_, lean_object* v_as_2548_, lean_object* v_sz_2549_, lean_object* v_i_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_){
_start:
{
size_t v_sz_boxed_2553_; size_t v_i_boxed_2554_; lean_object* v_res_2555_; 
v_sz_boxed_2553_ = lean_unbox_usize(v_sz_2549_);
lean_dec(v_sz_2549_);
v_i_boxed_2554_ = lean_unbox_usize(v_i_2550_);
lean_dec(v_i_2550_);
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2547_, v_as_2548_, v_sz_boxed_2553_, v_i_boxed_2554_, v_b_2551_);
lean_dec_ref(v_as_2548_);
lean_dec_ref(v_a_2547_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2556_, lean_object* v_as_2557_, size_t v_sz_2558_, size_t v_i_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_usize_dec_lt(v_i_2559_, v_sz_2558_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_b_2560_);
return v___x_2567_;
}
else
{
lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2586_; 
v_snd_2568_ = lean_ctor_get(v_b_2560_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_b_2560_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v_b_2560_, 0);
lean_dec(v_unused_2587_);
v___x_2570_ = v_b_2560_;
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_dec(v_b_2560_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v_a_2574_; lean_object* v_a_2581_; 
v___x_2572_ = lean_box(0);
v_a_2581_ = lean_array_uget_borrowed(v_as_2557_, v_i_2559_);
if (lean_obj_tag(v_a_2581_) == 0)
{
v_a_2574_ = v_snd_2568_;
goto v___jp_2573_;
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_val_2582_ = lean_ctor_get(v_a_2581_, 0);
v___x_2583_ = l_Lean_LocalDecl_fvarId(v_val_2582_);
v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2556_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_dec(v___x_2583_);
v_a_2574_ = v_snd_2568_;
goto v___jp_2573_;
}
else
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_array_push(v_snd_2568_, v___x_2583_);
v_a_2574_ = v___x_2585_;
goto v___jp_2573_;
}
}
v___jp_2573_:
{
lean_object* v___x_2576_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v_a_2574_);
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2576_ = v___x_2570_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2574_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_add(v_i_2559_, v___x_2577_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2556_, v_as_2557_, v_sz_2558_, v___x_2578_, v___x_2576_);
return v___x_2579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2588_, lean_object* v_as_2589_, lean_object* v_sz_2590_, lean_object* v_i_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
size_t v_sz_boxed_2598_; size_t v_i_boxed_2599_; lean_object* v_res_2600_; 
v_sz_boxed_2598_ = lean_unbox_usize(v_sz_2590_);
lean_dec(v_sz_2590_);
v_i_boxed_2599_ = lean_unbox_usize(v_i_2591_);
lean_dec(v_i_2591_);
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2588_, v_as_2589_, v_sz_boxed_2598_, v_i_boxed_2599_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v_as_2589_);
lean_dec_ref(v_a_2588_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2601_, lean_object* v_t_2602_, lean_object* v_init_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_root_2609_; lean_object* v_tail_2610_; lean_object* v___x_2611_; 
v_root_2609_ = lean_ctor_get(v_t_2602_, 0);
v_tail_2610_ = lean_ctor_get(v_t_2602_, 1);
lean_inc_ref(v_init_2603_);
v___x_2611_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2603_, v_a_2601_, v_root_2609_, v_init_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v_init_2603_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2648_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2648_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2648_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
if (lean_obj_tag(v_a_2612_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; 
v_a_2616_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v_a_2612_, 1);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_a_2616_);
v___x_2618_ = v___x_2614_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; size_t v_sz_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
lean_del_object(v___x_2614_);
v_a_2620_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v_a_2612_, 1);
v___x_2621_ = lean_box(0);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v_a_2620_);
v_sz_2623_ = lean_array_size(v_tail_2610_);
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2601_, v_tail_2610_, v_sz_2623_, v___x_2624_, v___x_2622_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2639_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2639_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2639_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_fst_2630_; 
v_fst_2630_ = lean_ctor_get(v_a_2626_, 0);
if (lean_obj_tag(v_fst_2630_) == 0)
{
lean_object* v_snd_2631_; lean_object* v___x_2633_; 
v_snd_2631_ = lean_ctor_get(v_a_2626_, 1);
lean_inc(v_snd_2631_);
lean_dec(v_a_2626_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_snd_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_snd_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
else
{
lean_object* v_val_2635_; lean_object* v___x_2637_; 
lean_inc_ref(v_fst_2630_);
lean_dec(v_a_2626_);
v_val_2635_ = lean_ctor_get(v_fst_2630_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v_fst_2630_, 1);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v_val_2635_);
v___x_2637_ = v___x_2628_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_val_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2625_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2625_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_a_2649_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2611_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2611_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2657_, lean_object* v_t_2658_, lean_object* v_init_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2657_, v_t_2658_, v_init_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec_ref(v_t_2658_);
lean_dec_ref(v_a_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2668_, lean_object* v_mvarId_2669_, lean_object* v___f_2670_, lean_object* v___f_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_lctx_2677_; lean_object* v_decls_2678_; lean_object* v___x_2679_; 
v_lctx_2677_ = lean_ctor_get(v___y_2672_, 2);
v_decls_2678_ = lean_ctor_get(v_lctx_2677_, 1);
lean_inc_ref(v_decls_2678_);
v___x_2679_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2678_, v_candidates_2668_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = l_Lean_MVarId_getType(v_mvarId_2669_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v_a_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___y_2688_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2682_, v___y_2673_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref(v___x_2683_);
v___x_2685_ = l_Lean_Expr_hasFVar(v_a_2684_);
v___x_2686_ = lean_st_mk_ref(v_a_2680_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v_a_2684_);
lean_dec_ref(v___f_2671_);
v___x_2712_ = lean_box(0);
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
lean_inc(v___y_2673_);
lean_inc_ref(v___y_2672_);
lean_inc(v___x_2686_);
v___x_2713_ = lean_apply_7(v___f_2670_, v___x_2712_, v___x_2686_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, lean_box(0));
v___y_2688_ = v___x_2713_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2715_ = 0;
v___x_2716_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2714_, v___f_2671_, v_a_2684_, v___x_2715_, v___x_2686_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
lean_inc(v___y_2673_);
lean_inc_ref(v___y_2672_);
lean_inc(v___x_2686_);
v___x_2718_ = lean_apply_7(v___f_2670_, v_a_2717_, v___x_2686_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, lean_box(0));
v___y_2688_ = v___x_2718_;
goto v___jp_2687_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v___x_2686_);
lean_dec_ref(v_decls_2678_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___f_2670_);
v_a_2719_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2716_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2716_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
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
v___x_2698_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2689_, v_decls_2678_, v___x_2697_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v_decls_2678_);
lean_dec(v_a_2689_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_a_2689_);
lean_dec_ref(v_decls_2678_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
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
lean_dec_ref(v_decls_2678_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
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
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2680_);
lean_dec_ref(v_decls_2678_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___f_2671_);
lean_dec_ref(v___f_2670_);
v_a_2727_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2681_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2681_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v_decls_2678_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v___f_2671_);
lean_dec_ref(v___f_2670_);
lean_dec(v_mvarId_2669_);
v_a_2735_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2679_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2679_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2743_, lean_object* v_mvarId_2744_, lean_object* v___f_2745_, lean_object* v___f_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2743_, v_mvarId_2744_, v___f_2745_, v___f_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___f_2761_; lean_object* v___f_2762_; lean_object* v_candidates_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
v___f_2761_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2762_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2763_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2755_);
v___f_2764_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2764_, 0, v_candidates_2763_);
lean_closure_set(v___f_2764_, 1, v_mvarId_2755_);
lean_closure_set(v___f_2764_, 2, v___f_2762_);
lean_closure_set(v___f_2764_, 3, v___f_2761_);
v___x_2765_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2755_, v___f_2764_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2773_, lean_object* v_m_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2774_, v_a_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2777_, lean_object* v_m_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2777_, v_m_2778_, v_a_2779_);
lean_dec(v_a_2779_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2781_, lean_object* v_m_2782_, lean_object* v_a_2783_, lean_object* v_b_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2782_, v_a_2783_, v_b_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2786_, lean_object* v_m_2787_, lean_object* v_a_2788_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2787_, v_a_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2790_, lean_object* v_m_2791_, lean_object* v_a_2792_){
_start:
{
uint8_t v_res_2793_; lean_object* v_r_2794_; 
v_res_2793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2790_, v_m_2791_, v_a_2792_);
lean_dec(v_a_2792_);
lean_dec_ref(v_m_2791_);
v_r_2794_ = lean_box(v_res_2793_);
return v_r_2794_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2795_, lean_object* v_a_2796_, lean_object* v_x_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2796_, v_x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2799_, lean_object* v_a_2800_, lean_object* v_x_2801_){
_start:
{
uint8_t v_res_2802_; lean_object* v_r_2803_; 
v_res_2802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2799_, v_a_2800_, v_x_2801_);
lean_dec(v_x_2801_);
lean_dec(v_a_2800_);
v_r_2803_ = lean_box(v_res_2802_);
return v_r_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2804_, lean_object* v_a_2805_, lean_object* v_x_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2805_, v_x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2808_, lean_object* v_a_2809_, lean_object* v_x_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2808_, v_a_2809_, v_x_2810_);
lean_dec(v_a_2809_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2812_, lean_object* v_a_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2812_, v_a_2813_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2821_, lean_object* v_a_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2821_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec(v_a_2822_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2830_, lean_object* v_data_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2833_, lean_object* v_a_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2833_, v_a_2834_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2842_, lean_object* v_a_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2842_, v_a_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec(v_a_2843_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2851_, lean_object* v_i_2852_, lean_object* v_source_2853_, lean_object* v_target_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2852_, v_source_2853_, v_target_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2856_, lean_object* v_as_2857_, size_t v_sz_2858_, size_t v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2856_, v_as_2857_, v_sz_2858_, v_i_2859_, v_b_2860_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2867_, lean_object* v_as_2868_, lean_object* v_sz_2869_, lean_object* v_i_2870_, lean_object* v_b_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2869_);
lean_dec(v_sz_2869_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2870_);
lean_dec(v_i_2870_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2867_, v_as_2868_, v_sz_boxed_2877_, v_i_boxed_2878_, v_b_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v_as_2868_);
lean_dec_ref(v_a_2867_);
return v_res_2879_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2880_, lean_object* v_m_2881_, lean_object* v_a_2882_){
_start:
{
uint8_t v___x_2883_; 
v___x_2883_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2881_, v_a_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2884_, lean_object* v_m_2885_, lean_object* v_a_2886_){
_start:
{
uint8_t v_res_2887_; lean_object* v_r_2888_; 
v_res_2887_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2884_, v_m_2885_, v_a_2886_);
lean_dec_ref(v_a_2886_);
lean_dec_ref(v_m_2885_);
v_r_2888_ = lean_box(v_res_2887_);
return v_r_2888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2889_, lean_object* v_m_2890_, lean_object* v_a_2891_, lean_object* v_b_2892_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2890_, v_a_2891_, v_b_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2894_, lean_object* v_x_2895_, lean_object* v_x_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2895_, v_x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2898_, lean_object* v_as_2899_, size_t v_sz_2900_, size_t v_i_2901_, lean_object* v_b_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2898_, v_as_2899_, v_sz_2900_, v_i_2901_, v_b_2902_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2909_, lean_object* v_as_2910_, lean_object* v_sz_2911_, lean_object* v_i_2912_, lean_object* v_b_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
size_t v_sz_boxed_2919_; size_t v_i_boxed_2920_; lean_object* v_res_2921_; 
v_sz_boxed_2919_ = lean_unbox_usize(v_sz_2911_);
lean_dec(v_sz_2911_);
v_i_boxed_2920_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2909_, v_as_2910_, v_sz_boxed_2919_, v_i_boxed_2920_, v_b_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec_ref(v_as_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2921_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2922_, lean_object* v_a_2923_, lean_object* v_x_2924_){
_start:
{
uint8_t v___x_2925_; 
v___x_2925_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2923_, v_x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2926_, lean_object* v_a_2927_, lean_object* v_x_2928_){
_start:
{
uint8_t v_res_2929_; lean_object* v_r_2930_; 
v_res_2929_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2926_, v_a_2927_, v_x_2928_);
lean_dec(v_x_2928_);
lean_dec_ref(v_a_2927_);
v_r_2930_ = lean_box(v_res_2929_);
return v_r_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2931_, lean_object* v_data_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2934_, lean_object* v_i_2935_, lean_object* v_source_2936_, lean_object* v_target_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2935_, v_source_2936_, v_target_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2940_, v_x_2941_);
return v___x_2942_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = l_Lean_maxRecDepthErrorMessage;
v___x_2949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2951_ = l_Lean_MessageData_ofFormat(v___x_2950_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2953_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2954_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v___x_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2955_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v_ref_2955_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2963_, lean_object* v_ref_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2964_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_2972_, lean_object* v_ref_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_2972_, v_ref_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_2981_, lean_object* v_mvarId_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_toCold_2989_; lean_object* v_currRecDepth_2990_; lean_object* v_ref_2991_; uint16_t v_optionFlags_2992_; uint8_t v_suppressElabErrors_2993_; uint8_t v_isRecordingDeps_2994_; lean_object* v_maxRecDepth_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v_toCold_2989_ = lean_ctor_get(v_a_2986_, 0);
v_currRecDepth_2990_ = lean_ctor_get(v_a_2986_, 1);
v_ref_2991_ = lean_ctor_get(v_a_2986_, 2);
v_optionFlags_2992_ = lean_ctor_get_uint16(v_a_2986_, sizeof(void*)*3);
v_suppressElabErrors_2993_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2994_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*3 + 3);
v_maxRecDepth_3022_ = lean_ctor_get(v_toCold_2989_, 3);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = lean_nat_dec_eq(v_maxRecDepth_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_nat_dec_eq(v_currRecDepth_2990_, v_maxRecDepth_3022_);
if (v___x_3025_ == 0)
{
goto v___jp_2995_;
}
else
{
lean_object* v___x_3026_; 
lean_dec(v_mvarId_2982_);
lean_dec_ref(v_x_2981_);
lean_inc(v_ref_2991_);
v___x_3026_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2991_);
return v___x_3026_;
}
}
else
{
goto v___jp_2995_;
}
v___jp_2995_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2996_ = lean_unsigned_to_nat(1u);
v___x_2997_ = lean_nat_add(v_currRecDepth_2990_, v___x_2996_);
lean_inc(v_ref_2991_);
lean_inc_ref(v_toCold_2989_);
v___x_2998_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2998_, 0, v_toCold_2989_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
lean_ctor_set(v___x_2998_, 2, v_ref_2991_);
lean_ctor_set_uint16(v___x_2998_, sizeof(void*)*3, v_optionFlags_2992_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*3 + 2, v_suppressElabErrors_2993_);
lean_ctor_set_uint8(v___x_2998_, sizeof(void*)*3 + 3, v_isRecordingDeps_2994_);
lean_inc_ref(v_x_2981_);
lean_inc(v_a_2987_);
lean_inc_ref(v___x_2998_);
lean_inc(v_a_2985_);
lean_inc_ref(v_a_2984_);
lean_inc(v_mvarId_2982_);
v___x_2999_ = lean_apply_6(v_x_2981_, v_mvarId_2982_, v_a_2984_, v_a_2985_, v___x_2998_, v_a_2987_, lean_box(0));
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3013_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
if (lean_obj_tag(v_a_3000_) == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
lean_dec_ref_known(v___x_2998_, 3);
lean_dec_ref(v_x_2981_);
v___x_3004_ = lean_st_ref_take(v_a_2983_);
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_array_push(v___x_3004_, v_mvarId_2982_);
v___x_3007_ = lean_st_ref_put(v_a_2983_, v___x_3006_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3005_);
v___x_3009_ = v___x_3002_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3005_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
else
{
lean_object* v_val_3011_; lean_object* v___x_3012_; 
lean_del_object(v___x_3002_);
lean_dec(v_mvarId_2982_);
v_val_3011_ = lean_ctor_get(v_a_3000_, 0);
lean_inc(v_val_3011_);
lean_dec_ref_known(v_a_3000_, 1);
v___x_3012_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_2981_, v_val_3011_, v_a_2983_, v_a_2984_, v_a_2985_, v___x_2998_, v_a_2987_);
lean_dec_ref_known(v___x_2998_, 3);
return v___x_3012_;
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref_known(v___x_2998_, 3);
lean_dec(v_mvarId_2982_);
lean_dec_ref(v_x_2981_);
v_a_3014_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2999_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2999_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3027_, lean_object* v_as_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
if (lean_obj_tag(v_as_3028_) == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref(v_x_3027_);
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
return v___x_3036_;
}
else
{
lean_object* v_head_3037_; lean_object* v_tail_3038_; lean_object* v___x_3039_; 
v_head_3037_ = lean_ctor_get(v_as_3028_, 0);
lean_inc(v_head_3037_);
v_tail_3038_ = lean_ctor_get(v_as_3028_, 1);
lean_inc(v_tail_3038_);
lean_dec_ref_known(v_as_3028_, 2);
lean_inc_ref(v_x_3027_);
v___x_3039_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3027_, v_head_3037_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_dec_ref_known(v___x_3039_, 1);
v_as_3028_ = v_tail_3038_;
goto _start;
}
else
{
lean_dec(v_tail_3038_);
lean_dec_ref(v_x_3027_);
return v___x_3039_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3041_, lean_object* v_as_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3041_, v_as_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3050_, lean_object* v_mvarId_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3050_, v_mvarId_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3059_, lean_object* v_x_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3067_ = lean_st_mk_ref(v___x_3066_);
v___x_3068_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3060_, v_mvarId_3059_, v___x_3067_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3077_; 
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3068_, 0);
lean_dec(v_unused_3078_);
v___x_3070_ = v___x_3068_;
v_isShared_3071_ = v_isSharedCheck_3077_;
goto v_resetjp_3069_;
}
else
{
lean_dec(v___x_3068_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3077_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3072_ = lean_st_ref_get(v___x_3067_);
lean_dec(v___x_3067_);
v___x_3073_ = lean_array_to_list(v___x_3072_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3073_);
v___x_3075_ = v___x_3070_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v___x_3067_);
v_a_3079_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3068_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3068_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3087_, lean_object* v_x_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_Meta_saturate(v_mvarId_3087_, v_x_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3095_, lean_object* v_msg_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
if (lean_obj_tag(v_mvarIds_3095_) == 1)
{
lean_object* v_tail_3102_; 
v_tail_3102_ = lean_ctor_get(v_mvarIds_3095_, 1);
if (lean_obj_tag(v_tail_3102_) == 0)
{
lean_object* v_head_3103_; lean_object* v___x_3104_; 
lean_dec_ref(v_msg_3096_);
v_head_3103_ = lean_ctor_get(v_mvarIds_3095_, 0);
lean_inc(v_head_3103_);
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_head_3103_);
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3105_;
}
}
else
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3107_, lean_object* v_msg_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Meta_exactlyOne(v_mvarIds_3107_, v_msg_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec(v_mvarIds_3107_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3115_, lean_object* v_msg_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
if (lean_obj_tag(v_mvarIds_3115_) == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_msg_3116_);
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
return v___x_3123_;
}
else
{
lean_object* v_tail_3124_; 
v_tail_3124_ = lean_ctor_get(v_mvarIds_3115_, 1);
if (lean_obj_tag(v_tail_3124_) == 0)
{
lean_object* v_head_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec_ref(v_msg_3116_);
v_head_3125_ = lean_ctor_get(v_mvarIds_3115_, 0);
lean_inc(v_head_3125_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_head_3125_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
return v___x_3127_;
}
else
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3129_, lean_object* v_msg_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3129_, v_msg_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_mvarIds_3129_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3137_, size_t v_sz_3138_, size_t v_i_3139_, lean_object* v_b_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
uint8_t v___x_3146_; 
v___x_3146_ = lean_usize_dec_lt(v_i_3139_, v_sz_3138_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_b_3140_);
return v___x_3147_;
}
else
{
lean_object* v_snd_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3178_; 
v_snd_3148_ = lean_ctor_get(v_b_3140_, 1);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_b_3140_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v_b_3140_, 0);
lean_dec(v_unused_3179_);
v___x_3150_ = v_b_3140_;
v_isShared_3151_ = v_isSharedCheck_3178_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_snd_3148_);
lean_dec(v_b_3140_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3178_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v_a_3154_; lean_object* v_a_3161_; 
v___x_3152_ = lean_box(0);
v_a_3161_ = lean_array_uget_borrowed(v_as_3137_, v_i_3139_);
if (lean_obj_tag(v_a_3161_) == 0)
{
v_a_3154_ = v_snd_3148_;
goto v___jp_3153_;
}
else
{
lean_object* v_val_3162_; uint8_t v___x_3163_; 
v_val_3162_ = lean_ctor_get(v_a_3161_, 0);
v___x_3163_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = l_Lean_LocalDecl_type(v_val_3162_);
v___x_3165_ = l_Lean_Meta_isProp(v___x_3164_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; uint8_t v___x_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = lean_unbox(v_a_3166_);
lean_dec(v_a_3166_);
if (v___x_3167_ == 0)
{
v_a_3154_ = v_snd_3148_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = l_Lean_LocalDecl_fvarId(v_val_3162_);
v___x_3169_ = lean_array_push(v_snd_3148_, v___x_3168_);
v_a_3154_ = v___x_3169_;
goto v___jp_3153_;
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_del_object(v___x_3150_);
lean_dec(v_snd_3148_);
v_a_3170_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3165_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3165_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
v_a_3154_ = v_snd_3148_;
goto v___jp_3153_;
}
}
v___jp_3153_:
{
lean_object* v___x_3156_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v_a_3154_);
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3156_ = v___x_3150_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_a_3154_);
v___x_3156_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
size_t v___x_3157_; size_t v___x_3158_; 
v___x_3157_ = ((size_t)1ULL);
v___x_3158_ = lean_usize_add(v_i_3139_, v___x_3157_);
v_i_3139_ = v___x_3158_;
v_b_3140_ = v___x_3156_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3180_, lean_object* v_sz_3181_, lean_object* v_i_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; lean_object* v_res_3191_; 
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3181_);
lean_dec(v_sz_3181_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3182_);
lean_dec(v_i_3182_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3180_, v_sz_boxed_3189_, v_i_boxed_3190_, v_b_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v_as_3180_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3192_, size_t v_sz_3193_, size_t v_i_3194_, lean_object* v_b_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
uint8_t v___x_3201_; 
v___x_3201_ = lean_usize_dec_lt(v_i_3194_, v_sz_3193_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v_b_3195_);
return v___x_3202_;
}
else
{
lean_object* v_snd_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3233_; 
v_snd_3203_ = lean_ctor_get(v_b_3195_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_b_3195_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v_b_3195_, 0);
lean_dec(v_unused_3234_);
v___x_3205_ = v_b_3195_;
v_isShared_3206_ = v_isSharedCheck_3233_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_snd_3203_);
lean_dec(v_b_3195_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3233_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v_a_3209_; lean_object* v_a_3216_; 
v___x_3207_ = lean_box(0);
v_a_3216_ = lean_array_uget_borrowed(v_as_3192_, v_i_3194_);
if (lean_obj_tag(v_a_3216_) == 0)
{
v_a_3209_ = v_snd_3203_;
goto v___jp_3208_;
}
else
{
lean_object* v_val_3217_; uint8_t v___x_3218_; 
v_val_3217_ = lean_ctor_get(v_a_3216_, 0);
v___x_3218_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = l_Lean_LocalDecl_type(v_val_3217_);
v___x_3220_ = l_Lean_Meta_isProp(v___x_3219_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; uint8_t v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = lean_unbox(v_a_3221_);
lean_dec(v_a_3221_);
if (v___x_3222_ == 0)
{
v_a_3209_ = v_snd_3203_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = l_Lean_LocalDecl_fvarId(v_val_3217_);
v___x_3224_ = lean_array_push(v_snd_3203_, v___x_3223_);
v_a_3209_ = v___x_3224_;
goto v___jp_3208_;
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_del_object(v___x_3205_);
lean_dec(v_snd_3203_);
v_a_3225_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3220_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3220_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
else
{
v_a_3209_ = v_snd_3203_;
goto v___jp_3208_;
}
}
v___jp_3208_:
{
lean_object* v___x_3211_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 1, v_a_3209_);
lean_ctor_set(v___x_3205_, 0, v___x_3207_);
v___x_3211_ = v___x_3205_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_a_3209_);
v___x_3211_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
size_t v___x_3212_; size_t v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = ((size_t)1ULL);
v___x_3213_ = lean_usize_add(v_i_3194_, v___x_3212_);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3192_, v_sz_3193_, v___x_3213_, v___x_3211_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
return v___x_3214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3235_, lean_object* v_sz_3236_, lean_object* v_i_3237_, lean_object* v_b_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
size_t v_sz_boxed_3244_; size_t v_i_boxed_3245_; lean_object* v_res_3246_; 
v_sz_boxed_3244_ = lean_unbox_usize(v_sz_3236_);
lean_dec(v_sz_3236_);
v_i_boxed_3245_ = lean_unbox_usize(v_i_3237_);
lean_dec(v_i_3237_);
v_res_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3235_, v_sz_boxed_3244_, v_i_boxed_3245_, v_b_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec_ref(v_as_3235_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3247_, lean_object* v_n_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
if (lean_obj_tag(v_n_3248_) == 0)
{
lean_object* v_cs_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; size_t v_sz_3258_; size_t v___x_3259_; lean_object* v___x_3260_; 
v_cs_3255_ = lean_ctor_get(v_n_3248_, 0);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v_b_3249_);
v_sz_3258_ = lean_array_size(v_cs_3255_);
v___x_3259_ = ((size_t)0ULL);
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3247_, v_cs_3255_, v_sz_3258_, v___x_3259_, v___x_3257_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3275_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3275_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3275_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v_fst_3265_; 
v_fst_3265_ = lean_ctor_get(v_a_3261_, 0);
if (lean_obj_tag(v_fst_3265_) == 0)
{
lean_object* v_snd_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v_snd_3266_ = lean_ctor_get(v_a_3261_, 1);
lean_inc(v_snd_3266_);
lean_dec(v_a_3261_);
v___x_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_snd_3266_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3267_);
v___x_3269_ = v___x_3263_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
else
{
lean_object* v_val_3271_; lean_object* v___x_3273_; 
lean_inc_ref(v_fst_3265_);
lean_dec(v_a_3261_);
v_val_3271_ = lean_ctor_get(v_fst_3265_, 0);
lean_inc(v_val_3271_);
lean_dec_ref_known(v_fst_3265_, 1);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_val_3271_);
v___x_3273_ = v___x_3263_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_val_3271_);
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
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
v_a_3276_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3260_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3260_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
else
{
lean_object* v_vs_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; size_t v_sz_3287_; size_t v___x_3288_; lean_object* v___x_3289_; 
v_vs_3284_ = lean_ctor_get(v_n_3248_, 0);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v_b_3249_);
v_sz_3287_ = lean_array_size(v_vs_3284_);
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3284_, v_sz_3287_, v___x_3288_, v___x_3286_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3304_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3304_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3304_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_fst_3294_; 
v_fst_3294_ = lean_ctor_get(v_a_3290_, 0);
if (lean_obj_tag(v_fst_3294_) == 0)
{
lean_object* v_snd_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v_snd_3295_ = lean_ctor_get(v_a_3290_, 1);
lean_inc(v_snd_3295_);
lean_dec(v_a_3290_);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v_snd_3295_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3296_);
v___x_3298_ = v___x_3292_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
else
{
lean_object* v_val_3300_; lean_object* v___x_3302_; 
lean_inc_ref(v_fst_3294_);
lean_dec(v_a_3290_);
v_val_3300_ = lean_ctor_get(v_fst_3294_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v_fst_3294_, 1);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_val_3300_);
v___x_3302_ = v___x_3292_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_val_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
v_a_3305_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3289_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3289_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3313_, lean_object* v_as_3314_, size_t v_sz_3315_, size_t v_i_3316_, lean_object* v_b_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_usize_dec_lt(v_i_3316_, v_sz_3315_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v_b_3317_);
return v___x_3324_;
}
else
{
lean_object* v_snd_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3359_; 
v_snd_3325_ = lean_ctor_get(v_b_3317_, 1);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_b_3317_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v_b_3317_, 0);
lean_dec(v_unused_3360_);
v___x_3327_ = v_b_3317_;
v_isShared_3328_ = v_isSharedCheck_3359_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_snd_3325_);
lean_dec(v_b_3317_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3359_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v_a_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_box(0);
v_a_3330_ = lean_array_uget_borrowed(v_as_3314_, v_i_3316_);
lean_inc(v_snd_3325_);
v___x_3331_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3313_, v_a_3330_, v_snd_3325_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3350_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3350_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3350_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_a_3332_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3336_);
v___x_3338_ = v___x_3327_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_snd_3325_);
v___x_3338_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3340_; 
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3338_);
v___x_3340_ = v___x_3334_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; 
lean_del_object(v___x_3334_);
lean_dec(v_snd_3325_);
v_a_3343_ = lean_ctor_get(v_a_3332_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v_a_3332_, 1);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v_a_3343_);
lean_ctor_set(v___x_3327_, 0, v___x_3329_);
v___x_3345_ = v___x_3327_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3343_);
v___x_3345_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
size_t v___x_3346_; size_t v___x_3347_; 
v___x_3346_ = ((size_t)1ULL);
v___x_3347_ = lean_usize_add(v_i_3316_, v___x_3346_);
v_i_3316_ = v___x_3347_;
v_b_3317_ = v___x_3345_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_del_object(v___x_3327_);
lean_dec(v_snd_3325_);
v_a_3351_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3331_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3331_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3361_, lean_object* v_as_3362_, lean_object* v_sz_3363_, lean_object* v_i_3364_, lean_object* v_b_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
size_t v_sz_boxed_3371_; size_t v_i_boxed_3372_; lean_object* v_res_3373_; 
v_sz_boxed_3371_ = lean_unbox_usize(v_sz_3363_);
lean_dec(v_sz_3363_);
v_i_boxed_3372_ = lean_unbox_usize(v_i_3364_);
lean_dec(v_i_3364_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3361_, v_as_3362_, v_sz_boxed_3371_, v_i_boxed_3372_, v_b_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec_ref(v_as_3362_);
lean_dec_ref(v_init_3361_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3374_, lean_object* v_n_3375_, lean_object* v_b_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3374_, v_n_3375_, v_b_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec_ref(v_n_3375_);
lean_dec_ref(v_init_3374_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3383_, size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_b_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v_b_3386_);
return v___x_3393_;
}
else
{
lean_object* v_snd_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3424_; 
v_snd_3394_ = lean_ctor_get(v_b_3386_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_b_3386_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v_b_3386_, 0);
lean_dec(v_unused_3425_);
v___x_3396_ = v_b_3386_;
v_isShared_3397_ = v_isSharedCheck_3424_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_snd_3394_);
lean_dec(v_b_3386_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3424_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v_a_3400_; lean_object* v_a_3407_; 
v___x_3398_ = lean_box(0);
v_a_3407_ = lean_array_uget_borrowed(v_as_3383_, v_i_3385_);
if (lean_obj_tag(v_a_3407_) == 0)
{
v_a_3400_ = v_snd_3394_;
goto v___jp_3399_;
}
else
{
lean_object* v_val_3408_; uint8_t v___x_3409_; 
v_val_3408_ = lean_ctor_get(v_a_3407_, 0);
v___x_3409_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = l_Lean_LocalDecl_type(v_val_3408_);
v___x_3411_ = l_Lean_Meta_isProp(v___x_3410_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; uint8_t v___x_3413_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = lean_unbox(v_a_3412_);
lean_dec(v_a_3412_);
if (v___x_3413_ == 0)
{
v_a_3400_ = v_snd_3394_;
goto v___jp_3399_;
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = l_Lean_LocalDecl_fvarId(v_val_3408_);
v___x_3415_ = lean_array_push(v_snd_3394_, v___x_3414_);
v_a_3400_ = v___x_3415_;
goto v___jp_3399_;
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_del_object(v___x_3396_);
lean_dec(v_snd_3394_);
v_a_3416_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3411_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3411_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
v_a_3400_ = v_snd_3394_;
goto v___jp_3399_;
}
}
v___jp_3399_:
{
lean_object* v___x_3402_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_a_3400_);
lean_ctor_set(v___x_3396_, 0, v___x_3398_);
v___x_3402_ = v___x_3396_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_a_3400_);
v___x_3402_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
size_t v___x_3403_; size_t v___x_3404_; 
v___x_3403_ = ((size_t)1ULL);
v___x_3404_ = lean_usize_add(v_i_3385_, v___x_3403_);
v_i_3385_ = v___x_3404_;
v_b_3386_ = v___x_3402_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3426_, lean_object* v_sz_3427_, lean_object* v_i_3428_, lean_object* v_b_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
size_t v_sz_boxed_3435_; size_t v_i_boxed_3436_; lean_object* v_res_3437_; 
v_sz_boxed_3435_ = lean_unbox_usize(v_sz_3427_);
lean_dec(v_sz_3427_);
v_i_boxed_3436_ = lean_unbox_usize(v_i_3428_);
lean_dec(v_i_3428_);
v_res_3437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3426_, v_sz_boxed_3435_, v_i_boxed_3436_, v_b_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec_ref(v_as_3426_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3438_, size_t v_sz_3439_, size_t v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_usize_dec_lt(v_i_3440_, v_sz_3439_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_b_3441_);
return v___x_3448_;
}
else
{
lean_object* v_snd_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3479_; 
v_snd_3449_ = lean_ctor_get(v_b_3441_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_b_3441_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v_b_3441_, 0);
lean_dec(v_unused_3480_);
v___x_3451_ = v_b_3441_;
v_isShared_3452_ = v_isSharedCheck_3479_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3449_);
lean_dec(v_b_3441_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3479_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v_a_3455_; lean_object* v_a_3462_; 
v___x_3453_ = lean_box(0);
v_a_3462_ = lean_array_uget_borrowed(v_as_3438_, v_i_3440_);
if (lean_obj_tag(v_a_3462_) == 0)
{
v_a_3455_ = v_snd_3449_;
goto v___jp_3454_;
}
else
{
lean_object* v_val_3463_; uint8_t v___x_3464_; 
v_val_3463_ = lean_ctor_get(v_a_3462_, 0);
v___x_3464_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = l_Lean_LocalDecl_type(v_val_3463_);
v___x_3466_ = l_Lean_Meta_isProp(v___x_3465_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; uint8_t v___x_3468_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
v___x_3468_ = lean_unbox(v_a_3467_);
lean_dec(v_a_3467_);
if (v___x_3468_ == 0)
{
v_a_3455_ = v_snd_3449_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = l_Lean_LocalDecl_fvarId(v_val_3463_);
v___x_3470_ = lean_array_push(v_snd_3449_, v___x_3469_);
v_a_3455_ = v___x_3470_;
goto v___jp_3454_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_del_object(v___x_3451_);
lean_dec(v_snd_3449_);
v_a_3471_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3466_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3466_);
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
v_a_3455_ = v_snd_3449_;
goto v___jp_3454_;
}
}
v___jp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v_a_3455_);
lean_ctor_set(v___x_3451_, 0, v___x_3453_);
v___x_3457_ = v___x_3451_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_a_3455_);
v___x_3457_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3440_, v___x_3458_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3438_, v_sz_3439_, v___x_3459_, v___x_3457_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
return v___x_3460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3481_, lean_object* v_sz_3482_, lean_object* v_i_3483_, lean_object* v_b_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
size_t v_sz_boxed_3490_; size_t v_i_boxed_3491_; lean_object* v_res_3492_; 
v_sz_boxed_3490_ = lean_unbox_usize(v_sz_3482_);
lean_dec(v_sz_3482_);
v_i_boxed_3491_ = lean_unbox_usize(v_i_3483_);
lean_dec(v_i_3483_);
v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3481_, v_sz_boxed_3490_, v_i_boxed_3491_, v_b_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_as_3481_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3493_, lean_object* v_init_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_root_3500_; lean_object* v_tail_3501_; lean_object* v___x_3502_; 
v_root_3500_ = lean_ctor_get(v_t_3493_, 0);
v_tail_3501_ = lean_ctor_get(v_t_3493_, 1);
lean_inc_ref(v_init_3494_);
v___x_3502_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3494_, v_root_3500_, v_init_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec_ref(v_init_3494_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3539_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3539_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3539_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
if (lean_obj_tag(v_a_3503_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; 
v_a_3507_ = lean_ctor_get(v_a_3503_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v_a_3503_, 1);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v_a_3507_);
v___x_3509_ = v___x_3505_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; size_t v_sz_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
lean_del_object(v___x_3505_);
v_a_3511_ = lean_ctor_get(v_a_3503_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v_a_3503_, 1);
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
lean_ctor_set(v___x_3513_, 1, v_a_3511_);
v_sz_3514_ = lean_array_size(v_tail_3501_);
v___x_3515_ = ((size_t)0ULL);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3501_, v_sz_3514_, v___x_3515_, v___x_3513_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3530_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3530_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3530_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v_fst_3521_; 
v_fst_3521_ = lean_ctor_get(v_a_3517_, 0);
if (lean_obj_tag(v_fst_3521_) == 0)
{
lean_object* v_snd_3522_; lean_object* v___x_3524_; 
v_snd_3522_ = lean_ctor_get(v_a_3517_, 1);
lean_inc(v_snd_3522_);
lean_dec(v_a_3517_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v_snd_3522_);
v___x_3524_ = v___x_3519_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_snd_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
else
{
lean_object* v_val_3526_; lean_object* v___x_3528_; 
lean_inc_ref(v_fst_3521_);
lean_dec(v_a_3517_);
v_val_3526_ = lean_ctor_get(v_fst_3521_, 0);
lean_inc(v_val_3526_);
lean_dec_ref_known(v_fst_3521_, 1);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v_val_3526_);
v___x_3528_ = v___x_3519_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_val_3526_);
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
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3516_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3516_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3502_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3502_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3548_, lean_object* v_init_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3548_, v_init_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v_t_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_lctx_3561_; lean_object* v_decls_3562_; lean_object* v_result_3563_; lean_object* v___x_3564_; 
v_lctx_3561_ = lean_ctor_get(v_a_3556_, 2);
v_decls_3562_ = lean_ctor_get(v_lctx_3561_, 1);
v_result_3563_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3564_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3562_, v_result_3563_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Meta_getPropHyps(v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
return v_res_3570_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3575_ = l_Lean_MessageData_ofFormat(v___x_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3578_, lean_object* v___x_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; 
lean_inc(v___x_3579_);
lean_inc(v_mvarId_3578_);
v___x_3585_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3578_, v___x_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v___x_3586_; 
lean_dec_ref_known(v___x_3585_, 1);
lean_inc(v_mvarId_3578_);
v___x_3586_ = l_Lean_MVarId_getType(v_mvarId_3578_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___x_3586_, 1);
v___x_3588_ = lean_box(0);
v___x_3589_ = l_Lean_Meta_synthInstance(v_a_3587_, v___x_3588_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3589_, 1);
lean_inc(v_mvarId_3578_);
v___x_3591_ = l_Lean_mkMVar(v_mvarId_3578_);
v___x_3592_ = l_Lean_Meta_isExprDefEq(v___x_3591_, v_a_3590_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3604_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3595_ = v___x_3592_;
v_isShared_3596_ = v_isSharedCheck_3604_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3592_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3604_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
uint8_t v___x_3597_; 
v___x_3597_ = lean_unbox(v_a_3593_);
lean_dec(v_a_3593_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_del_object(v___x_3595_);
v___x_3598_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3599_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3579_, v_mvarId_3578_, v___x_3598_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
return v___x_3599_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
lean_dec(v___x_3579_);
lean_dec(v_mvarId_3578_);
v___x_3600_ = lean_box(0);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v___x_3600_);
v___x_3602_ = v___x_3595_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
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
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v___x_3579_);
lean_dec(v_mvarId_3578_);
v_a_3605_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3592_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3592_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v___x_3579_);
lean_dec(v_mvarId_3578_);
v_a_3613_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3589_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3589_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v___x_3579_);
lean_dec(v_mvarId_3578_);
v_a_3621_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3586_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3586_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_dec(v___x_3579_);
lean_dec(v_mvarId_3578_);
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3629_, lean_object* v___x_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3629_, v___x_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v___x_3646_; lean_object* v___f_3647_; lean_object* v___x_3648_; 
v___x_3646_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3640_);
v___f_3647_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3647_, 0, v_mvarId_3640_);
lean_closure_set(v___f_3647_, 1, v___x_3646_);
v___x_3648_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3640_, v___f_3647_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_MVarId_inferInstance(v_mvarId_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl(lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_obj_tag_nat(v_x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl___boxed(lean_object* v_x_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_Meta_TacticResultCNM_ctorIdx___impl(v_x_3658_);
lean_dec(v_x_3658_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3660_, lean_object* v_k_3661_){
_start:
{
if (lean_obj_tag(v_t_3660_) == 2)
{
lean_object* v_mvarId_3662_; lean_object* v___x_3663_; 
v_mvarId_3662_ = lean_ctor_get(v_t_3660_, 0);
lean_inc(v_mvarId_3662_);
lean_dec_ref_known(v_t_3660_, 1);
v___x_3663_ = lean_apply_1(v_k_3661_, v_mvarId_3662_);
return v___x_3663_;
}
else
{
lean_dec(v_t_3660_);
return v_k_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3664_, lean_object* v_ctorIdx_3665_, lean_object* v_t_3666_, lean_object* v_h_3667_, lean_object* v_k_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3666_, v_k_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3670_, lean_object* v_ctorIdx_3671_, lean_object* v_t_3672_, lean_object* v_h_3673_, lean_object* v_k_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3670_, v_ctorIdx_3671_, v_t_3672_, v_h_3673_, v_k_3674_);
lean_dec(v_ctorIdx_3671_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3676_, lean_object* v_closed_3677_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3676_, v_closed_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3679_, lean_object* v_t_3680_, lean_object* v_h_3681_, lean_object* v_closed_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3680_, v_closed_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3684_, lean_object* v_noChange_3685_){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3684_, v_noChange_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3687_, lean_object* v_t_3688_, lean_object* v_h_3689_, lean_object* v_noChange_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3688_, v_noChange_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3692_, lean_object* v_modified_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3692_, v_modified_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3695_, lean_object* v_t_3696_, lean_object* v_h_3697_, lean_object* v_modified_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3696_, v_modified_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_a_3710_; lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_MVarId_getType(v_g_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3721_ = lean_mk_empty_array_with_capacity(v___x_3720_);
v___x_3722_ = lean_array_push(v___x_3721_, v_a_3718_);
v___x_3723_ = l_Lean_Meta_mkAppM(v___x_3719_, v___x_3722_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v___x_3725_ = lean_box(0);
v___x_3726_ = l_Lean_Meta_synthInstance(v_a_3724_, v___x_3725_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3735_; 
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v___x_3726_, 0);
lean_dec(v_unused_3736_);
v___x_3728_ = v___x_3726_;
v_isShared_3729_ = v_isSharedCheck_3735_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v___x_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3735_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
uint8_t v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3730_ = 1;
v___x_3731_ = lean_box(v___x_3730_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3731_);
v___x_3733_ = v___x_3728_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
else
{
lean_object* v_a_3737_; 
v_a_3737_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3726_, 1);
v_a_3710_ = v_a_3737_;
goto v___jp_3709_;
}
}
else
{
lean_object* v_a_3738_; 
v_a_3738_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3723_, 1);
v_a_3710_ = v_a_3738_;
goto v___jp_3709_;
}
}
else
{
lean_object* v_a_3739_; 
v_a_3739_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3717_, 1);
v_a_3710_ = v_a_3739_;
goto v___jp_3709_;
}
v___jp_3709_:
{
uint8_t v___x_3711_; 
v___x_3711_ = l_Lean_Exception_isInterrupt(v_a_3710_);
if (v___x_3711_ == 0)
{
uint8_t v___x_3712_; 
lean_inc_ref(v_a_3710_);
v___x_3712_ = l_Lean_Exception_isRuntime(v_a_3710_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_dec_ref(v_a_3710_);
v___x_3713_ = lean_box(v___x_3712_);
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_a_3710_);
return v___x_3715_;
}
}
else
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_a_3710_);
return v___x_3716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_MVarId_isSubsingleton(v_g_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3767_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3764_, v___x_3765_, v___x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3769_;
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
