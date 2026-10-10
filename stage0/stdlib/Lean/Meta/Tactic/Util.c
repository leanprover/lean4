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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
return v_res_60_;
}
}
lean_object* l_Lean_MVarId_getTag(lean_object* v_mvarId_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_MVarId_getDecl(v_mvarId_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_userName_72_; lean_object* v___x_74_; 
v_userName_72_ = lean_ctor_get(v_a_68_, 0);
lean_inc(v_userName_72_);
lean_dec(v_a_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v_userName_72_);
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_userName_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_a_77_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_67_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_67_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_getTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_61_ = stack[0].m_obj;
lean_object* v_a_62_ = stack[1].m_obj;
lean_object* v_a_63_ = stack[2].m_obj;
lean_object* v_a_64_ = stack[3].m_obj;
lean_object* v_a_65_ = stack[4].m_obj;
lean_object* v_res_85_;
v_res_85_ = l_Lean_MVarId_getTag(v_mvarId_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object* v_mvarId_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_MVarId_getTag(v_mvarId_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
return v_res_92_;
}
}
lean_object* l_Lean_MVarId_setTag___redArg(lean_object* v_mvarId_93_, lean_object* v_tag_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; lean_object* v_mctx_98_; lean_object* v_cache_99_; lean_object* v_zetaDeltaFVarIds_100_; lean_object* v_postponed_101_; lean_object* v_diag_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_113_; 
v___x_97_ = lean_st_ref_take(v_a_95_);
v_mctx_98_ = lean_ctor_get(v___x_97_, 0);
v_cache_99_ = lean_ctor_get(v___x_97_, 1);
v_zetaDeltaFVarIds_100_ = lean_ctor_get(v___x_97_, 2);
v_postponed_101_ = lean_ctor_get(v___x_97_, 3);
v_diag_102_ = lean_ctor_get(v___x_97_, 4);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_113_ == 0)
{
v___x_104_ = v___x_97_;
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_diag_102_);
lean_inc(v_postponed_101_);
lean_inc(v_zetaDeltaFVarIds_100_);
lean_inc(v_cache_99_);
lean_inc(v_mctx_98_);
lean_dec(v___x_97_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_98_, v_mvarId_93_, v_tag_94_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_cache_99_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_zetaDeltaFVarIds_100_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_postponed_101_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v_diag_102_);
v___x_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_st_ref_put(v_a_95_, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_106_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_setTag___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_93_ = stack[0].m_obj;
lean_object* v_tag_94_ = stack[1].m_obj;
lean_object* v_a_95_ = stack[2].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_MVarId_setTag___redArg(v_mvarId_93_, v_tag_94_, v_a_95_);
stack->m_obj
 = v_res_114_;
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
lean_object* l_Lean_MVarId_setTag(lean_object* v_mvarId_120_, lean_object* v_tag_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_MVarId_setTag___redArg(v_mvarId_120_, v_tag_121_, v_a_123_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_MVarId_setTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_120_ = stack[0].m_obj;
lean_object* v_tag_121_ = stack[1].m_obj;
lean_object* v_a_122_ = stack[2].m_obj;
lean_object* v_a_123_ = stack[3].m_obj;
lean_object* v_a_124_ = stack[4].m_obj;
lean_object* v_a_125_ = stack[5].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_MVarId_setTag(v_mvarId_120_, v_tag_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object* v_mvarId_129_, lean_object* v_tag_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_MVarId_setTag(v_mvarId_129_, v_tag_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object* v_suffix_137_, lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = l_Lean_Name_eraseMacroScopes(v_suffix_137_);
v___x_140_ = l_Lean_Name_append(v_x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object* v_suffix_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_appendTag___lam__0(v_suffix_141_, v_x_142_);
lean_dec(v_suffix_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_144_, lean_object* v_suffix_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = l_Lean_Name_hasMacroScopes(v_tag_144_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_appendTag___lam__0(v_suffix_145_, v_tag_144_);
return v___x_147_;
}
else
{
lean_object* v_view_148_; lean_object* v_name_149_; lean_object* v_imported_150_; lean_object* v_ctx_151_; lean_object* v_scopes_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_161_; 
v_view_148_ = l_Lean_extractMacroScopes(v_tag_144_);
v_name_149_ = lean_ctor_get(v_view_148_, 0);
v_imported_150_ = lean_ctor_get(v_view_148_, 1);
v_ctx_151_ = lean_ctor_get(v_view_148_, 2);
v_scopes_152_ = lean_ctor_get(v_view_148_, 3);
v_isSharedCheck_161_ = !lean_is_exclusive(v_view_148_);
if (v_isSharedCheck_161_ == 0)
{
v___x_154_ = v_view_148_;
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_scopes_152_);
lean_inc(v_ctx_151_);
lean_inc(v_imported_150_);
lean_inc(v_name_149_);
lean_dec(v_view_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = l_Lean_Meta_appendTag___lam__0(v_suffix_145_, v_name_149_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_imported_150_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_ctx_151_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v_scopes_152_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_MacroScopesView_review(v___x_158_);
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object* v_tag_162_, lean_object* v_suffix_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Meta_appendTag(v_tag_162_, v_suffix_163_);
lean_dec(v_suffix_163_);
return v_res_164_;
}
}
lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_165_, lean_object* v_suffix_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v_mvarId_165_);
v___x_172_ = l_Lean_MVarId_getTag(v_mvarId_165_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = l_Lean_Meta_appendTag(v_a_173_, v_suffix_166_);
v___x_175_ = l_Lean_MVarId_setTag___redArg(v_mvarId_165_, v___x_174_, v_a_168_);
return v___x_175_;
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_mvarId_165_);
v_a_176_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_172_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_appendTagSuffix_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_165_ = stack[0].m_obj;
lean_object* v_suffix_166_ = stack[1].m_obj;
lean_object* v_a_167_ = stack[2].m_obj;
lean_object* v_a_168_ = stack[3].m_obj;
lean_object* v_a_169_ = stack[4].m_obj;
lean_object* v_a_170_ = stack[5].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Meta_appendTagSuffix(v_mvarId_165_, v_suffix_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_185_, lean_object* v_suffix_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Meta_appendTagSuffix(v_mvarId_185_, v_suffix_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_suffix_186_);
return v_res_192_;
}
}
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_193_, lean_object* v_tag_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_type_193_);
v___x_201_ = 2;
v___x_202_ = l_Lean_Meta_mkFreshExprMVar(v___x_200_, v___x_201_, v_tag_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
return v___x_202_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_193_ = stack[0].m_obj;
lean_object* v_tag_194_ = stack[1].m_obj;
lean_object* v_a_195_ = stack[2].m_obj;
lean_object* v_a_196_ = stack[3].m_obj;
lean_object* v_a_197_ = stack[4].m_obj;
lean_object* v_a_198_ = stack[5].m_obj;
lean_object* v_res_203_;
v_res_203_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_193_, v_tag_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_204_, lean_object* v_tag_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_204_, v_tag_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_211_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_221_, lean_object* v_mvarId_222_, lean_object* v_msg_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_224_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_225_ = l_Lean_MessageData_ofName(v_tacticName_221_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_msg_223_);
v___x_230_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_mvarId_222_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v_env_241_; uint8_t v___x_242_; lean_object* v_env_243_; lean_object* v___x_244_; lean_object* v_toCold_245_; lean_object* v_mctx_246_; lean_object* v_lctx_247_; lean_object* v_options_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_240_ = lean_st_ref_get(v___y_238_);
v_env_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_env_241_);
lean_dec(v___x_240_);
v___x_242_ = 0;
v_env_243_ = l_Lean_Environment_setRecordingDeps(v_env_241_, v___x_242_);
v___x_244_ = lean_st_ref_get(v___y_236_);
v_toCold_245_ = lean_ctor_get(v___y_237_, 0);
v_mctx_246_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref(v_mctx_246_);
lean_dec(v___x_244_);
v_lctx_247_ = lean_ctor_get(v___y_235_, 2);
v_options_248_ = lean_ctor_get(v_toCold_245_, 2);
lean_inc_ref(v_options_248_);
lean_inc_ref(v_lctx_247_);
v___x_249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_249_, 0, v_env_243_);
lean_ctor_set(v___x_249_, 1, v_mctx_246_);
lean_ctor_set(v___x_249_, 2, v_lctx_247_);
lean_ctor_set(v___x_249_, 3, v_options_248_);
v___x_250_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_msgData_234_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_234_ = stack[0].m_obj;
lean_object* v___y_235_ = stack[1].m_obj;
lean_object* v___y_236_ = stack[2].m_obj;
lean_object* v___y_237_ = stack[3].m_obj;
lean_object* v___y_238_ = stack[4].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_ref_266_; lean_object* v___x_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_ref_266_ = lean_ctor_get(v___y_263_, 2);
v___x_267_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_inc(v_ref_266_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_ref_266_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 1);
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_260_ = stack[0].m_obj;
lean_object* v___y_261_ = stack[1].m_obj;
lean_object* v___y_262_ = stack[2].m_obj;
lean_object* v___y_263_ = stack[3].m_obj;
lean_object* v___y_264_ = stack[4].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_288_, lean_object* v_mvarId_289_, lean_object* v_msg_x3f_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
if (lean_obj_tag(v_msg_x3f_290_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_296_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_297_ = l_Lean_MessageData_ofName(v_tacticName_288_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v_mvarId_289_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_302_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
return v___x_303_;
}
else
{
lean_object* v_val_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_val_304_ = lean_ctor_get(v_msg_x3f_290_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v_msg_x3f_290_, 1);
v___x_305_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_288_, v_mvarId_289_, v_val_304_);
v___x_306_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_305_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
return v___x_306_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_throwTacticEx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_288_ = stack[0].m_obj;
lean_object* v_mvarId_289_ = stack[1].m_obj;
lean_object* v_msg_x3f_290_ = stack[2].m_obj;
lean_object* v_a_291_ = stack[3].m_obj;
lean_object* v_a_292_ = stack[4].m_obj;
lean_object* v_a_293_ = stack[5].m_obj;
lean_object* v_a_294_ = stack[6].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_288_, v_mvarId_289_, v_msg_x3f_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_308_, lean_object* v_mvarId_309_, lean_object* v_msg_x3f_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_308_, v_mvarId_309_, v_msg_x3f_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_316_;
}
}
lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_317_, lean_object* v_tacticName_318_, lean_object* v_mvarId_319_, lean_object* v_msg_x3f_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_318_, v_mvarId_319_, v_msg_x3f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwTacticEx_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_318_ = stack[1].m_obj;
lean_object* v_mvarId_319_ = stack[2].m_obj;
lean_object* v_msg_x3f_320_ = stack[3].m_obj;
lean_object* v_a_321_ = stack[4].m_obj;
lean_object* v_a_322_ = stack[5].m_obj;
lean_object* v_a_323_ = stack[6].m_obj;
lean_object* v_a_324_ = stack[7].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_Meta_throwTacticEx(lean_box(0), v_tacticName_318_, v_mvarId_319_, v_msg_x3f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_328_, lean_object* v_tacticName_329_, lean_object* v_mvarId_330_, lean_object* v_msg_x3f_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_328_, v_tacticName_329_, v_mvarId_330_, v_msg_x3f_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_337_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_338_, lean_object* v_msg_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_339_ = stack[1].m_obj;
lean_object* v___y_340_ = stack[2].m_obj;
lean_object* v___y_341_ = stack[3].m_obj;
lean_object* v___y_342_ = stack[4].m_obj;
lean_object* v___y_343_ = stack[5].m_obj;
lean_object* v_res_346_;
v_res_346_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_box(0), v_msg_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_347_, v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_357_ = l_Lean_stringToMessageData(v___x_356_);
return v___x_357_;
}
}
lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_361_, lean_object* v_ex_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_nestedMsg_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_msg_374_; lean_object* v_kind_375_; uint8_t v___x_376_; 
v_nestedMsg_368_ = l_Lean_Exception_toMessageData(v_ex_362_);
v___x_369_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_370_ = l_Lean_MessageData_ofName(v_tacticName_361_);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
lean_inc_ref(v_nestedMsg_368_);
v_msg_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_374_, 0, v___x_373_);
lean_ctor_set(v_msg_374_, 1, v_nestedMsg_368_);
v_kind_375_ = l_Lean_MessageData_kind(v_nestedMsg_368_);
lean_dec_ref(v_nestedMsg_368_);
v___x_376_ = l_Lean_Name_isAnonymous(v_kind_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_378_ = l_Lean_Name_append(v___x_377_, v_kind_375_);
v___x_379_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_msg_374_);
v___x_380_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_379_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
lean_dec(v_kind_375_);
v___x_381_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_374_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_381_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_throwNestedTacticEx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_361_ = stack[0].m_obj;
lean_object* v_ex_362_ = stack[1].m_obj;
lean_object* v_a_363_ = stack[2].m_obj;
lean_object* v_a_364_ = stack[3].m_obj;
lean_object* v_a_365_ = stack[4].m_obj;
lean_object* v_a_366_ = stack[5].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_361_, v_ex_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_383_, lean_object* v_ex_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_383_, v_ex_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_391_, lean_object* v_tacticName_392_, lean_object* v_ex_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_392_, v_ex_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwNestedTacticEx_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_392_ = stack[1].m_obj;
lean_object* v_ex_393_ = stack[2].m_obj;
lean_object* v_a_394_ = stack[3].m_obj;
lean_object* v_a_395_ = stack[4].m_obj;
lean_object* v_a_396_ = stack[5].m_obj;
lean_object* v_a_397_ = stack[6].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Meta_throwNestedTacticEx(lean_box(0), v_tacticName_392_, v_ex_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_401_, lean_object* v_tacticName_402_, lean_object* v_ex_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_401_, v_tacticName_402_, v_ex_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_409_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_410_, lean_object* v_i_411_, lean_object* v_k_412_){
_start:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_keys_410_);
v___x_414_ = lean_nat_dec_lt(v_i_411_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec(v_i_411_);
return v___x_414_;
}
else
{
lean_object* v_k_x27_415_; uint8_t v___x_416_; 
v_k_x27_415_ = lean_array_fget_borrowed(v_keys_410_, v_i_411_);
v___x_416_ = l_Lean_instBEqMVarId_beq(v_k_412_, v_k_x27_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v_i_411_, v___x_417_);
lean_dec(v_i_411_);
v_i_411_ = v___x_418_;
goto _start;
}
else
{
lean_dec(v_i_411_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_410_ = stack[0].m_obj;
lean_object* v_i_411_ = stack[1].m_obj;
lean_object* v_k_412_ = stack[2].m_obj;
uint8_t v_res_420_;
v_res_420_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_410_, v_i_411_, v_k_412_);
stack->m_num = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_421_, lean_object* v_i_422_, lean_object* v_k_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_421_, v_i_422_, v_k_423_);
lean_dec(v_k_423_);
lean_dec_ref(v_keys_421_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_426_, size_t v_x_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_es_429_; lean_object* v___x_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v_j_433_; lean_object* v___x_434_; 
v_es_429_ = lean_ctor_get(v_x_426_, 0);
v___x_430_ = lean_box(2);
v___x_431_ = ((size_t)31ULL);
v___x_432_ = lean_usize_land(v_x_427_, v___x_431_);
v_j_433_ = lean_usize_to_nat(v___x_432_);
v___x_434_ = lean_array_get_borrowed(v___x_430_, v_es_429_, v_j_433_);
lean_dec(v_j_433_);
switch(lean_obj_tag(v___x_434_))
{
case 0:
{
lean_object* v_key_435_; uint8_t v___x_436_; 
v_key_435_ = lean_ctor_get(v___x_434_, 0);
v___x_436_ = l_Lean_instBEqMVarId_beq(v_x_428_, v_key_435_);
return v___x_436_;
}
case 1:
{
lean_object* v_node_437_; size_t v___x_438_; size_t v___x_439_; 
v_node_437_ = lean_ctor_get(v___x_434_, 0);
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_usize_shift_right(v_x_427_, v___x_438_);
v_x_426_ = v_node_437_;
v_x_427_ = v___x_439_;
goto _start;
}
default: 
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
}
}
else
{
lean_object* v_ks_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_ks_442_ = lean_ctor_get(v_x_426_, 0);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_442_, v___x_443_, v_x_428_);
return v___x_444_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_426_ = stack[0].m_obj;
size_t v_x_427_ = stack[1].m_num;
lean_object* v_x_428_ = stack[2].m_obj;
uint8_t v_res_445_;
v_res_445_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_426_, v_x_427_, v_x_428_);
stack->m_num = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
size_t v_x_552__boxed_449_; uint8_t v_res_450_; lean_object* v_r_451_; 
v_x_552__boxed_449_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_res_450_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_446_, v_x_552__boxed_449_, v_x_448_);
lean_dec(v_x_448_);
lean_dec_ref(v_x_446_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint64_t v___x_454_; size_t v___x_455_; uint8_t v___x_456_; 
v___x_454_ = l_Lean_instHashableMVarId_hash(v_x_453_);
v___x_455_ = lean_uint64_to_usize(v___x_454_);
v___x_456_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_452_, v___x_455_, v_x_453_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_452_ = stack[0].m_obj;
lean_object* v_x_453_ = stack[1].m_obj;
uint8_t v_res_457_;
v_res_457_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_452_, v_x_453_);
stack->m_num = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
uint8_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_458_, v_x_459_);
lean_dec(v_x_459_);
lean_dec_ref(v_x_458_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; lean_object* v_mctx_466_; lean_object* v_eAssignment_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = lean_st_ref_get(v___y_463_);
v_mctx_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_mctx_466_);
lean_dec(v___x_465_);
v_eAssignment_467_ = lean_ctor_get(v_mctx_466_, 8);
lean_inc_ref(v_eAssignment_467_);
lean_dec_ref(v_mctx_466_);
v___x_468_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_467_, v_mvarId_462_);
lean_dec_ref(v_eAssignment_467_);
v___x_469_ = lean_box(v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_462_ = stack[0].m_obj;
lean_object* v___y_463_ = stack[1].m_obj;
lean_object* v_res_471_;
v_res_471_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_462_, v___y_463_);
stack->m_obj
 = v_res_471_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec(v_mvarId_472_);
return v_res_475_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_483_ = l_Lean_MessageData_ofFormat(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_485_ = l_Lean_MessageData_note(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_487_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_491_, lean_object* v_tacticName_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_510_; 
v___x_498_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_491_, v_a_494_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_510_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v___x_503_; 
v___x_503_ = lean_unbox(v_a_499_);
lean_dec(v_a_499_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec(v_tacticName_492_);
lean_dec(v_mvarId_491_);
v___x_504_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_del_object(v___x_501_);
v___x_508_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_509_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_492_, v_mvarId_491_, v___x_508_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_checkNotAssigned_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_491_ = stack[0].m_obj;
lean_object* v_tacticName_492_ = stack[1].m_obj;
lean_object* v_a_493_ = stack[2].m_obj;
lean_object* v_a_494_ = stack[3].m_obj;
lean_object* v_a_495_ = stack[4].m_obj;
lean_object* v_a_496_ = stack[5].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_491_, v_tacticName_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_512_, lean_object* v_tacticName_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_512_, v_tacticName_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
return v_res_519_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_520_, v___y_522_);
return v___x_526_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_520_ = stack[0].m_obj;
lean_object* v___y_521_ = stack[1].m_obj;
lean_object* v___y_522_ = stack[2].m_obj;
lean_object* v___y_523_ = stack[3].m_obj;
lean_object* v___y_524_ = stack[4].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v_mvarId_528_);
return v_res_534_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_536_, v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_536_ = stack[1].m_obj;
lean_object* v_x_537_ = stack[2].m_obj;
uint8_t v_res_539_;
v_res_539_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_box(0), v_x_536_, v_x_537_);
stack->m_num = v_res_539_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_540_, v_x_541_, v_x_542_);
lean_dec(v_x_542_);
lean_dec_ref(v_x_541_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_545_, lean_object* v_x_546_, size_t v_x_547_, lean_object* v_x_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_546_, v_x_547_, v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_546_ = stack[1].m_obj;
size_t v_x_547_ = stack[2].m_num;
lean_object* v_x_548_ = stack[3].m_obj;
uint8_t v_res_550_;
v_res_550_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_box(0), v_x_546_, v_x_547_, v_x_548_);
stack->m_num = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
size_t v_x_801__boxed_555_; uint8_t v_res_556_; lean_object* v_r_557_; 
v_x_801__boxed_555_ = lean_unbox_usize(v_x_553_);
lean_dec(v_x_553_);
v_res_556_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_551_, v_x_552_, v_x_801__boxed_555_, v_x_554_);
lean_dec(v_x_554_);
lean_dec_ref(v_x_552_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_558_, lean_object* v_keys_559_, lean_object* v_vals_560_, lean_object* v_heq_561_, lean_object* v_i_562_, lean_object* v_k_563_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_559_, v_i_562_, v_k_563_);
return v___x_564_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_559_ = stack[1].m_obj;
lean_object* v_vals_560_ = stack[2].m_obj;
lean_object* v_i_562_ = stack[4].m_obj;
lean_object* v_k_563_ = stack[5].m_obj;
uint8_t v_res_565_;
v_res_565_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_keys_559_, v_vals_560_, lean_box(0), v_i_562_, v_k_563_);
stack->m_num = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_566_, lean_object* v_keys_567_, lean_object* v_vals_568_, lean_object* v_heq_569_, lean_object* v_i_570_, lean_object* v_k_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_566_, v_keys_567_, v_vals_568_, v_heq_569_, v_i_570_, v_k_571_);
lean_dec(v_k_571_);
lean_dec_ref(v_vals_568_);
lean_dec_ref(v_keys_567_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_MVarId_getDecl(v_mvarId_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_589_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_type_585_; lean_object* v___x_587_; 
v_type_585_ = lean_ctor_get(v_a_581_, 2);
lean_inc_ref(v_type_585_);
lean_dec(v_a_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_type_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_type_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_580_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_580_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_getType_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_574_ = stack[0].m_obj;
lean_object* v_a_575_ = stack[1].m_obj;
lean_object* v_a_576_ = stack[2].m_obj;
lean_object* v_a_577_ = stack[3].m_obj;
lean_object* v_a_578_ = stack[4].m_obj;
lean_object* v_res_598_;
v_res_598_ = l_Lean_MVarId_getType(v_mvarId_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_MVarId_getType(v_mvarId_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_605_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_606_, lean_object* v___y_607_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Expr_hasMVar(v_e_606_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_e_606_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v_mctx_612_; lean_object* v___x_613_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___x_616_; lean_object* v_cache_617_; lean_object* v_zetaDeltaFVarIds_618_; lean_object* v_postponed_619_; lean_object* v_diag_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_629_; 
v___x_611_ = lean_st_ref_get(v___y_607_);
v_mctx_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc_ref(v_mctx_612_);
lean_dec(v___x_611_);
v___x_613_ = l_Lean_instantiateMVarsCore(v_mctx_612_, v_e_606_);
v_fst_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_fst_614_);
v_snd_615_ = lean_ctor_get(v___x_613_, 1);
lean_inc(v_snd_615_);
lean_dec_ref(v___x_613_);
v___x_616_ = lean_st_ref_take(v___y_607_);
v_cache_617_ = lean_ctor_get(v___x_616_, 1);
v_zetaDeltaFVarIds_618_ = lean_ctor_get(v___x_616_, 2);
v_postponed_619_ = lean_ctor_get(v___x_616_, 3);
v_diag_620_ = lean_ctor_get(v___x_616_, 4);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_616_, 0);
lean_dec(v_unused_630_);
v___x_622_ = v___x_616_;
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_diag_620_);
lean_inc(v_postponed_619_);
lean_inc(v_zetaDeltaFVarIds_618_);
lean_inc(v_cache_617_);
lean_dec(v___x_616_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_snd_615_);
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_snd_615_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_zetaDeltaFVarIds_618_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_postponed_619_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v_diag_620_);
v___x_625_ = v_reuseFailAlloc_628_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_st_ref_put(v___y_607_, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_fst_614_);
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_606_ = stack[0].m_obj;
lean_object* v___y_607_ = stack[1].m_obj;
lean_object* v_res_631_;
v_res_631_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_606_, v___y_607_);
stack->m_obj
 = v_res_631_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_632_, v___y_633_);
lean_dec(v___y_633_);
return v_res_635_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_636_, v___y_638_);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_636_ = stack[0].m_obj;
lean_object* v___y_637_ = stack[1].m_obj;
lean_object* v___y_638_ = stack[2].m_obj;
lean_object* v___y_639_ = stack[3].m_obj;
lean_object* v___y_640_ = stack[4].m_obj;
lean_object* v_res_643_;
v_res_643_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_650_;
}
}
lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_MVarId_getType(v_mvarId_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
lean_inc(v_a_655_);
lean_inc_ref(v_a_654_);
lean_inc(v_a_653_);
lean_inc_ref(v_a_652_);
v___x_659_ = lean_whnf(v_a_658_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_660_, v_a_653_);
return v___x_661_;
}
else
{
return v___x_659_;
}
}
else
{
return v___x_657_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_getType_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_651_ = stack[0].m_obj;
lean_object* v_a_652_ = stack[1].m_obj;
lean_object* v_a_653_ = stack[2].m_obj;
lean_object* v_a_654_ = stack[3].m_obj;
lean_object* v_a_655_ = stack[4].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_MVarId_getType_x27(v_mvarId_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_MVarId_getType_x27(v_mvarId_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_669_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_736_ = 0;
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_738_ = l_Lean_registerTraceClass(v___x_735_, v___x_736_, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_739_;
v_res_739_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_741_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_742_, lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_742_, v_x_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_749_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_749_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_742_ = stack[0].m_obj;
lean_object* v_x_743_ = stack[1].m_obj;
lean_object* v___y_744_ = stack[2].m_obj;
lean_object* v___y_745_ = stack[3].m_obj;
lean_object* v___y_746_ = stack[4].m_obj;
lean_object* v___y_747_ = stack[5].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_742_, v_x_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_767_, lean_object* v_x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_767_, v_x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_775_, lean_object* v_mvarId_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_776_, v_x_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_783_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_776_ = stack[1].m_obj;
lean_object* v_x_777_ = stack[2].m_obj;
lean_object* v___y_778_ = stack[3].m_obj;
lean_object* v___y_779_ = stack[4].m_obj;
lean_object* v___y_780_ = stack[5].m_obj;
lean_object* v___y_781_ = stack[6].m_obj;
lean_object* v_res_784_;
v_res_784_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_box(0), v_mvarId_776_, v_x_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_785_, lean_object* v_mvarId_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_785_, v_mvarId_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_ks_798_; lean_object* v_vs_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_823_; 
v_ks_798_ = lean_ctor_get(v_x_794_, 0);
v_vs_799_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_823_ == 0)
{
v___x_801_ = v_x_794_;
v_isShared_802_ = v_isSharedCheck_823_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_vs_799_);
lean_inc(v_ks_798_);
lean_dec(v_x_794_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_823_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_get_size(v_ks_798_);
v___x_804_ = lean_nat_dec_lt(v_x_795_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_x_795_);
v___x_805_ = lean_array_push(v_ks_798_, v_x_796_);
v___x_806_ = lean_array_push(v_vs_799_, v_x_797_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_806_);
lean_ctor_set(v___x_801_, 0, v___x_805_);
v___x_808_ = v___x_801_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v_k_x27_810_; uint8_t v___x_811_; 
v_k_x27_810_ = lean_array_fget_borrowed(v_ks_798_, v_x_795_);
v___x_811_ = l_Lean_instBEqMVarId_beq(v_x_796_, v_k_x27_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_813_; 
if (v_isShared_802_ == 0)
{
v___x_813_ = v___x_801_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_ks_798_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_vs_799_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_x_795_, v___x_814_);
lean_dec(v_x_795_);
v_x_794_ = v___x_813_;
v_x_795_ = v___x_815_;
goto _start;
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_818_ = lean_array_fset(v_ks_798_, v_x_795_, v_x_796_);
v___x_819_ = lean_array_fset(v_vs_799_, v_x_795_, v_x_797_);
lean_dec(v_x_795_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v___x_819_);
lean_ctor_set(v___x_801_, 0, v___x_818_);
v___x_821_ = v___x_801_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_824_, lean_object* v_k_825_, lean_object* v_v_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_824_, v___x_827_, v_k_825_, v_v_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_829_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_830_, size_t v_x_831_, size_t v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v_es_835_; size_t v___x_836_; size_t v___x_837_; lean_object* v_j_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_es_835_ = lean_ctor_get(v_x_830_, 0);
v___x_836_ = ((size_t)31ULL);
v___x_837_ = lean_usize_land(v_x_831_, v___x_836_);
v_j_838_ = lean_usize_to_nat(v___x_837_);
v___x_839_ = lean_array_get_size(v_es_835_);
v___x_840_ = lean_nat_dec_lt(v_j_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_j_838_);
lean_dec(v_x_834_);
lean_dec(v_x_833_);
return v_x_830_;
}
else
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_879_; 
lean_inc_ref(v_es_835_);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_x_830_, 0);
lean_dec(v_unused_880_);
v___x_842_ = v_x_830_;
v_isShared_843_ = v_isSharedCheck_879_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_879_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_v_844_; lean_object* v___x_845_; lean_object* v_xs_x27_846_; lean_object* v___y_848_; 
v_v_844_ = lean_array_fget(v_es_835_, v_j_838_);
v___x_845_ = lean_box(0);
v_xs_x27_846_ = lean_array_fset(v_es_835_, v_j_838_, v___x_845_);
switch(lean_obj_tag(v_v_844_))
{
case 0:
{
lean_object* v_key_853_; lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v_key_853_ = lean_ctor_get(v_v_844_, 0);
v_val_854_ = lean_ctor_get(v_v_844_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_v_844_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v_v_844_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_inc(v_key_853_);
lean_dec(v_v_844_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; 
v___x_858_ = l_Lean_instBEqMVarId_beq(v_x_833_, v_key_853_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_del_object(v___x_856_);
v___x_859_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_853_, v_val_854_, v_x_833_, v_x_834_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
v___y_848_ = v___x_860_;
goto v___jp_847_;
}
else
{
lean_object* v___x_862_; 
lean_dec(v_val_854_);
lean_dec(v_key_853_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v_x_834_);
lean_ctor_set(v___x_856_, 0, v_x_833_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_x_833_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_x_834_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v___y_848_ = v___x_862_;
goto v___jp_847_;
}
}
}
}
case 1:
{
lean_object* v_node_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_877_; 
v_node_865_ = lean_ctor_get(v_v_844_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_v_844_);
if (v_isSharedCheck_877_ == 0)
{
v___x_867_ = v_v_844_;
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_node_865_);
lean_dec(v_v_844_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_877_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_869_ = ((size_t)5ULL);
v___x_870_ = lean_usize_shift_right(v_x_831_, v___x_869_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_x_832_, v___x_871_);
v___x_873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_865_, v___x_870_, v___x_872_, v_x_833_, v_x_834_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_873_);
v___x_875_ = v___x_867_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v___y_848_ = v___x_875_;
goto v___jp_847_;
}
}
}
default: 
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v_x_833_);
lean_ctor_set(v___x_878_, 1, v_x_834_);
v___y_848_ = v___x_878_;
goto v___jp_847_;
}
}
v___jp_847_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_array_fset(v_xs_x27_846_, v_j_838_, v___y_848_);
lean_dec(v_j_838_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_849_);
v___x_851_ = v___x_842_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
else
{
lean_object* v_ks_881_; lean_object* v_vs_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_900_; 
v_ks_881_ = lean_ctor_get(v_x_830_, 0);
v_vs_882_ = lean_ctor_get(v_x_830_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_900_ == 0)
{
v___x_884_ = v_x_830_;
v_isShared_885_ = v_isSharedCheck_900_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_vs_882_);
lean_inc(v_ks_881_);
lean_dec(v_x_830_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_900_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_ks_881_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_vs_882_);
v___x_887_ = v_reuseFailAlloc_899_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v_newNode_888_; size_t v___x_889_; uint8_t v___x_890_; 
v_newNode_888_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_887_, v_x_833_, v_x_834_);
v___x_889_ = ((size_t)7ULL);
v___x_890_ = lean_usize_dec_le(v___x_889_, v_x_832_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_888_);
v___x_892_ = lean_unsigned_to_nat(4u);
v___x_893_ = lean_nat_dec_lt(v___x_891_, v___x_892_);
lean_dec(v___x_891_);
if (v___x_893_ == 0)
{
lean_object* v_ks_894_; lean_object* v_vs_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_ks_894_ = lean_ctor_get(v_newNode_888_, 0);
lean_inc_ref(v_ks_894_);
v_vs_895_ = lean_ctor_get(v_newNode_888_, 1);
lean_inc_ref(v_vs_895_);
lean_dec_ref(v_newNode_888_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_832_, v_ks_894_, v_vs_895_, v___x_896_, v___x_897_);
lean_dec_ref(v_vs_895_);
lean_dec_ref(v_ks_894_);
return v___x_898_;
}
else
{
return v_newNode_888_;
}
}
else
{
return v_newNode_888_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_830_ = stack[0].m_obj;
size_t v_x_831_ = stack[1].m_num;
size_t v_x_832_ = stack[2].m_num;
lean_object* v_x_833_ = stack[3].m_obj;
lean_object* v_x_834_ = stack[4].m_obj;
lean_object* v_res_901_;
v_res_901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_830_, v_x_831_, v_x_832_, v_x_833_, v_x_834_);
stack->m_obj
 = v_res_901_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_902_, lean_object* v_keys_903_, lean_object* v_vals_904_, lean_object* v_i_905_, lean_object* v_entries_906_){
_start:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_array_get_size(v_keys_903_);
v___x_908_ = lean_nat_dec_lt(v_i_905_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v_i_905_);
return v_entries_906_;
}
else
{
lean_object* v_k_909_; lean_object* v_v_910_; uint64_t v___x_911_; size_t v_h_912_; size_t v___x_913_; lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v_h_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_k_909_ = lean_array_fget_borrowed(v_keys_903_, v_i_905_);
v_v_910_ = lean_array_fget_borrowed(v_vals_904_, v_i_905_);
v___x_911_ = l_Lean_instHashableMVarId_hash(v_k_909_);
v_h_912_ = lean_uint64_to_usize(v___x_911_);
v___x_913_ = ((size_t)5ULL);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v_depth_902_, v___x_915_);
v___x_917_ = lean_usize_mul(v___x_913_, v___x_916_);
v_h_918_ = lean_usize_shift_right(v_h_912_, v___x_917_);
v___x_919_ = lean_nat_add(v_i_905_, v___x_914_);
lean_dec(v_i_905_);
lean_inc(v_v_910_);
lean_inc(v_k_909_);
v___x_920_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_906_, v_h_918_, v_depth_902_, v_k_909_, v_v_910_);
v_i_905_ = v___x_919_;
v_entries_906_ = v___x_920_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_902_ = stack[0].m_num;
lean_object* v_keys_903_ = stack[1].m_obj;
lean_object* v_vals_904_ = stack[2].m_obj;
lean_object* v_i_905_ = stack[3].m_obj;
lean_object* v_entries_906_ = stack[4].m_obj;
lean_object* v_res_922_;
v_res_922_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_902_, v_keys_903_, v_vals_904_, v_i_905_, v_entries_906_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_i_926_, lean_object* v_entries_927_){
_start:
{
size_t v_depth_boxed_928_; lean_object* v_res_929_; 
v_depth_boxed_928_ = lean_unbox_usize(v_depth_923_);
lean_dec(v_depth_923_);
v_res_929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_928_, v_keys_924_, v_vals_925_, v_i_926_, v_entries_927_);
lean_dec_ref(v_vals_925_);
lean_dec_ref(v_keys_924_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
size_t v_x_1091__boxed_935_; size_t v_x_1092__boxed_936_; lean_object* v_res_937_; 
v_x_1091__boxed_935_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_x_1092__boxed_936_ = lean_unbox_usize(v_x_932_);
lean_dec(v_x_932_);
v_res_937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_930_, v_x_1091__boxed_935_, v_x_1092__boxed_936_, v_x_933_, v_x_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
uint64_t v___x_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v___x_944_; 
v___x_941_ = l_Lean_instHashableMVarId_hash(v_x_939_);
v___x_942_ = lean_uint64_to_usize(v___x_941_);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_938_, v___x_942_, v___x_943_, v_x_939_, v_x_940_);
return v___x_944_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_945_, lean_object* v_val_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_mctx_950_; lean_object* v_cache_951_; lean_object* v_zetaDeltaFVarIds_952_; lean_object* v_postponed_953_; lean_object* v_diag_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_984_; 
v___x_949_ = lean_st_ref_take(v___y_947_);
v_mctx_950_ = lean_ctor_get(v___x_949_, 0);
v_cache_951_ = lean_ctor_get(v___x_949_, 1);
v_zetaDeltaFVarIds_952_ = lean_ctor_get(v___x_949_, 2);
v_postponed_953_ = lean_ctor_get(v___x_949_, 3);
v_diag_954_ = lean_ctor_get(v___x_949_, 4);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_984_ == 0)
{
v___x_956_ = v___x_949_;
v_isShared_957_ = v_isSharedCheck_984_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_diag_954_);
lean_inc(v_postponed_953_);
lean_inc(v_zetaDeltaFVarIds_952_);
lean_inc(v_cache_951_);
lean_inc(v_mctx_950_);
lean_dec(v___x_949_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_984_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_depth_958_; lean_object* v_levelAssignDepth_959_; lean_object* v_lmvarCounter_960_; lean_object* v_mvarCounter_961_; lean_object* v_lDecls_962_; lean_object* v_decls_963_; lean_object* v_userNames_964_; lean_object* v_lAssignment_965_; lean_object* v_eAssignment_966_; lean_object* v_dAssignment_967_; lean_object* v_instanceTypedMVars_968_; lean_object* v_synthNormMemo_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_983_; 
v_depth_958_ = lean_ctor_get(v_mctx_950_, 0);
v_levelAssignDepth_959_ = lean_ctor_get(v_mctx_950_, 1);
v_lmvarCounter_960_ = lean_ctor_get(v_mctx_950_, 2);
v_mvarCounter_961_ = lean_ctor_get(v_mctx_950_, 3);
v_lDecls_962_ = lean_ctor_get(v_mctx_950_, 4);
v_decls_963_ = lean_ctor_get(v_mctx_950_, 5);
v_userNames_964_ = lean_ctor_get(v_mctx_950_, 6);
v_lAssignment_965_ = lean_ctor_get(v_mctx_950_, 7);
v_eAssignment_966_ = lean_ctor_get(v_mctx_950_, 8);
v_dAssignment_967_ = lean_ctor_get(v_mctx_950_, 9);
v_instanceTypedMVars_968_ = lean_ctor_get(v_mctx_950_, 10);
v_synthNormMemo_969_ = lean_ctor_get(v_mctx_950_, 11);
v_isSharedCheck_983_ = !lean_is_exclusive(v_mctx_950_);
if (v_isSharedCheck_983_ == 0)
{
v___x_971_ = v_mctx_950_;
v_isShared_972_ = v_isSharedCheck_983_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_synthNormMemo_969_);
lean_inc(v_instanceTypedMVars_968_);
lean_inc(v_dAssignment_967_);
lean_inc(v_eAssignment_966_);
lean_inc(v_lAssignment_965_);
lean_inc(v_userNames_964_);
lean_inc(v_decls_963_);
lean_inc(v_lDecls_962_);
lean_inc(v_mvarCounter_961_);
lean_inc(v_lmvarCounter_960_);
lean_inc(v_levelAssignDepth_959_);
lean_inc(v_depth_958_);
lean_dec(v_mctx_950_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_983_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = lean_box(0);
v___x_974_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_966_, v_mvarId_945_, v_val_946_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 8, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_depth_958_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_levelAssignDepth_959_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_lmvarCounter_960_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_mvarCounter_961_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_lDecls_962_);
lean_ctor_set(v_reuseFailAlloc_982_, 5, v_decls_963_);
lean_ctor_set(v_reuseFailAlloc_982_, 6, v_userNames_964_);
lean_ctor_set(v_reuseFailAlloc_982_, 7, v_lAssignment_965_);
lean_ctor_set(v_reuseFailAlloc_982_, 8, v___x_974_);
lean_ctor_set(v_reuseFailAlloc_982_, 9, v_dAssignment_967_);
lean_ctor_set(v_reuseFailAlloc_982_, 10, v_instanceTypedMVars_968_);
lean_ctor_set(v_reuseFailAlloc_982_, 11, v_synthNormMemo_969_);
v___x_976_ = v_reuseFailAlloc_982_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_978_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_976_);
v___x_978_ = v___x_956_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_cache_951_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_zetaDeltaFVarIds_952_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_postponed_953_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_diag_954_);
v___x_978_ = v_reuseFailAlloc_981_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_st_ref_put(v___y_947_, v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_973_);
return v___x_980_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_945_ = stack[0].m_obj;
lean_object* v_val_946_ = stack[1].m_obj;
lean_object* v___y_947_ = stack[2].m_obj;
lean_object* v_res_985_;
v_res_985_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_945_, v_val_946_, v___y_947_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_986_, lean_object* v_val_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_986_, v_val_987_, v___y_988_);
lean_dec(v___y_988_);
return v_res_990_;
}
}
lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_991_, lean_object* v___x_992_, uint8_t v_synthetic_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
lean_inc(v_mvarId_991_);
v___x_999_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_991_, v___x_992_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref_known(v___x_999_, 1);
lean_inc(v_mvarId_991_);
v___x_1000_ = l_Lean_MVarId_getType(v_mvarId_991_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = 1;
v___x_1003_ = l_Lean_Meta_mkLabeledSorry(v_a_1001_, v_synthetic_993_, v___x_1002_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_991_, v_a_1004_, v___y_995_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_mvarId_991_);
v_a_1006_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1003_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1003_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_mvarId_991_);
v_a_1014_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1000_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1000_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_dec(v_mvarId_991_);
return v___x_999_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_admit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_991_ = stack[0].m_obj;
lean_object* v___x_992_ = stack[1].m_obj;
uint8_t v_synthetic_993_ = stack[2].m_num;
lean_object* v___y_994_ = stack[3].m_obj;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v___y_996_ = stack[5].m_obj;
lean_object* v___y_997_ = stack[6].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l_Lean_MVarId_admit___lam__0(v_mvarId_991_, v___x_992_, v_synthetic_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_1023_, lean_object* v___x_1024_, lean_object* v_synthetic_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_synthetic_boxed_1031_; lean_object* v_res_1032_; 
v_synthetic_boxed_1031_ = lean_unbox(v_synthetic_1025_);
v_res_1032_ = l_Lean_MVarId_admit___lam__0(v_mvarId_1023_, v___x_1024_, v_synthetic_boxed_1031_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1032_;
}
}
lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1036_, uint8_t v_synthetic_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; 
v___x_1043_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1044_ = lean_box(v_synthetic_1037_);
lean_inc(v_mvarId_1036_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1045_, 0, v_mvarId_1036_);
lean_closure_set(v___f_1045_, 1, v___x_1043_);
lean_closure_set(v___f_1045_, 2, v___x_1044_);
v___x_1046_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1036_, v___f_1045_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
return v___x_1046_;
}
}
LEAN_EXPORT void l_Lean_MVarId_admit_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1036_ = stack[0].m_obj;
uint8_t v_synthetic_1037_ = stack[1].m_num;
lean_object* v_a_1038_ = stack[2].m_obj;
lean_object* v_a_1039_ = stack[3].m_obj;
lean_object* v_a_1040_ = stack[4].m_obj;
lean_object* v_a_1041_ = stack[5].m_obj;
lean_object* v_res_1047_;
v_res_1047_ = l_Lean_MVarId_admit(v_mvarId_1036_, v_synthetic_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1048_, lean_object* v_synthetic_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
uint8_t v_synthetic_boxed_1055_; lean_object* v_res_1056_; 
v_synthetic_boxed_1055_ = lean_unbox(v_synthetic_1049_);
v_res_1056_ = l_Lean_MVarId_admit(v_mvarId_1048_, v_synthetic_boxed_1055_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1056_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1057_, lean_object* v_val_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1057_, v_val_1058_, v___y_1060_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1057_ = stack[0].m_obj;
lean_object* v_val_1058_ = stack[1].m_obj;
lean_object* v___y_1059_ = stack[2].m_obj;
lean_object* v___y_1060_ = stack[3].m_obj;
lean_object* v___y_1061_ = stack[4].m_obj;
lean_object* v___y_1062_ = stack[5].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1057_, v_val_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1066_, lean_object* v_val_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1066_, v_val_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1075_, v_x_1076_, v_x_1077_);
return v___x_1078_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, size_t v_x_1081_, size_t v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1080_, v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1080_ = stack[1].m_obj;
size_t v_x_1081_ = stack[2].m_num;
size_t v_x_1082_ = stack[3].m_num;
lean_object* v_x_1083_ = stack[4].m_obj;
lean_object* v_x_1084_ = stack[5].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_box(0), v_x_1080_, v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_1585__boxed_1093_; size_t v_x_1586__boxed_1094_; lean_object* v_res_1095_; 
v_x_1585__boxed_1093_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_x_1586__boxed_1094_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1087_, v_x_1088_, v_x_1585__boxed_1093_, v_x_1586__boxed_1094_, v_x_1091_, v_x_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1096_, lean_object* v_n_1097_, lean_object* v_k_1098_, lean_object* v_v_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1097_, v_k_1098_, v_v_1099_);
return v___x_1100_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1101_, size_t v_depth_1102_, lean_object* v_keys_1103_, lean_object* v_vals_1104_, lean_object* v_heq_1105_, lean_object* v_i_1106_, lean_object* v_entries_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1102_, v_keys_1103_, v_vals_1104_, v_i_1106_, v_entries_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1102_ = stack[1].m_num;
lean_object* v_keys_1103_ = stack[2].m_obj;
lean_object* v_vals_1104_ = stack[3].m_obj;
lean_object* v_i_1106_ = stack[5].m_obj;
lean_object* v_entries_1107_ = stack[6].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_depth_1102_, v_keys_1103_, v_vals_1104_, lean_box(0), v_i_1106_, v_entries_1107_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1110_, lean_object* v_depth_1111_, lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_heq_1114_, lean_object* v_i_1115_, lean_object* v_entries_1116_){
_start:
{
size_t v_depth_boxed_1117_; lean_object* v_res_1118_; 
v_depth_boxed_1117_ = lean_unbox_usize(v_depth_1111_);
lean_dec(v_depth_1111_);
v_res_1118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1110_, v_depth_boxed_1117_, v_keys_1112_, v_vals_1113_, v_heq_1114_, v_i_1115_, v_entries_1116_);
lean_dec_ref(v_vals_1113_);
lean_dec_ref(v_keys_1112_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1120_, v_x_1121_, v_x_1122_, v_x_1123_);
return v___x_1124_;
}
}
lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
lean_inc(v_mvarId_1125_);
v___x_1131_ = l_Lean_MVarId_getType(v_mvarId_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = l_Lean_Expr_headBeta(v_a_1132_);
v___x_1134_ = l_Lean_MVarId_setType___redArg(v_mvarId_1125_, v___x_1133_, v_a_1127_);
return v___x_1134_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_mvarId_1125_);
v_a_1135_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1131_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1131_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_headBetaType_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1125_ = stack[0].m_obj;
lean_object* v_a_1126_ = stack[1].m_obj;
lean_object* v_a_1127_ = stack[2].m_obj;
lean_object* v_a_1128_ = stack[3].m_obj;
lean_object* v_a_1129_ = stack[4].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_Lean_MVarId_headBetaType(v_mvarId_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_MVarId_headBetaType(v_mvarId_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1150_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1151_, lean_object* v_x_1152_){
_start:
{
if (lean_obj_tag(v_x_1152_) == 0)
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
return v___x_1153_;
}
else
{
lean_object* v_key_1154_; lean_object* v_tail_1155_; uint8_t v___x_1156_; 
v_key_1154_ = lean_ctor_get(v_x_1152_, 0);
v_tail_1155_ = lean_ctor_get(v_x_1152_, 2);
v___x_1156_ = l_Lean_instBEqFVarId_beq(v_key_1154_, v_a_1151_);
if (v___x_1156_ == 0)
{
v_x_1152_ = v_tail_1155_;
goto _start;
}
else
{
return v___x_1156_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1151_ = stack[0].m_obj;
lean_object* v_x_1152_ = stack[1].m_obj;
uint8_t v_res_1158_;
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1151_, v_x_1152_);
stack->m_num = v_res_1158_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
uint8_t v_res_1161_; lean_object* v_r_1162_; 
v_res_1161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1159_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec(v_a_1159_);
v_r_1162_ = lean_box(v_res_1161_);
return v_r_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1163_, lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
return v_x_1164_;
}
else
{
lean_object* v_key_1165_; lean_object* v_value_1166_; lean_object* v_tail_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
v_key_1165_ = lean_ctor_get(v_x_1164_, 0);
v_value_1166_ = lean_ctor_get(v_x_1164_, 1);
v_tail_1167_ = lean_ctor_get(v_x_1164_, 2);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v_x_1164_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_tail_1167_);
lean_inc(v_value_1166_);
lean_inc(v_key_1165_);
lean_dec(v_x_1164_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v___x_1171_; 
v___x_1171_ = l_Lean_instBEqFVarId_beq(v_key_1165_, v_a_1163_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1163_, v_tail_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 2, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_key_1165_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_value_1166_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
else
{
lean_del_object(v___x_1169_);
lean_dec(v_value_1166_);
lean_dec(v_key_1165_);
return v_tail_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1177_, v_x_1178_);
lean_dec(v_a_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_size_1182_; lean_object* v_buckets_1183_; lean_object* v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v_fold_1188_; uint64_t v___x_1189_; uint64_t v___x_1190_; uint64_t v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; lean_object* v_bkt_1197_; uint8_t v___x_1198_; 
v_size_1182_ = lean_ctor_get(v_m_1180_, 0);
v_buckets_1183_ = lean_ctor_get(v_m_1180_, 1);
v___x_1184_ = lean_array_get_size(v_buckets_1183_);
v___x_1185_ = l_Lean_instHashableFVarId_hash(v_a_1181_);
v___x_1186_ = 32ULL;
v___x_1187_ = lean_uint64_shift_right(v___x_1185_, v___x_1186_);
v_fold_1188_ = lean_uint64_xor(v___x_1185_, v___x_1187_);
v___x_1189_ = 16ULL;
v___x_1190_ = lean_uint64_shift_right(v_fold_1188_, v___x_1189_);
v___x_1191_ = lean_uint64_xor(v_fold_1188_, v___x_1190_);
v___x_1192_ = lean_uint64_to_usize(v___x_1191_);
v___x_1193_ = lean_usize_of_nat(v___x_1184_);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_sub(v___x_1193_, v___x_1194_);
v___x_1196_ = lean_usize_land(v___x_1192_, v___x_1195_);
v_bkt_1197_ = lean_array_uget_borrowed(v_buckets_1183_, v___x_1196_);
v___x_1198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1181_, v_bkt_1197_);
if (v___x_1198_ == 0)
{
return v_m_1180_;
}
else
{
lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1211_; 
lean_inc(v_bkt_1197_);
lean_inc_ref(v_buckets_1183_);
lean_inc(v_size_1182_);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_m_1180_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; lean_object* v_unused_1213_; 
v_unused_1212_ = lean_ctor_get(v_m_1180_, 1);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_m_1180_, 0);
lean_dec(v_unused_1213_);
v___x_1200_ = v_m_1180_;
v_isShared_1201_ = v_isSharedCheck_1211_;
goto v_resetjp_1199_;
}
else
{
lean_dec(v_m_1180_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1211_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v_buckets_x27_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1202_ = lean_box(0);
v_buckets_x27_1203_ = lean_array_uset(v_buckets_1183_, v___x_1196_, v___x_1202_);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_sub(v_size_1182_, v___x_1204_);
lean_dec(v_size_1182_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1181_, v_bkt_1197_);
v___x_1207_ = lean_array_uset(v_buckets_x27_1203_, v___x_1196_, v___x_1206_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1207_);
lean_ctor_set(v___x_1200_, 0, v___x_1205_);
v___x_1209_ = v___x_1200_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1214_, v_a_1215_);
lean_dec(v_a_1215_);
return v_res_1216_;
}
}
lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = lean_st_ref_take(v___y_1218_);
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Lean_Expr_fvarId_x21(v_e_1217_);
v___x_1227_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1224_, v___x_1226_);
lean_dec(v___x_1226_);
v___x_1228_ = lean_st_ref_put(v___y_1218_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1225_);
return v___x_1229_;
}
}
LEAN_EXPORT void l_Lean_MVarId_getNondepPropHyps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1217_ = stack[0].m_obj;
lean_object* v___y_1218_ = stack[1].m_obj;
lean_object* v___y_1219_ = stack[2].m_obj;
lean_object* v___y_1220_ = stack[3].m_obj;
lean_object* v___y_1221_ = stack[4].m_obj;
lean_object* v___y_1222_ = stack[5].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v_e_1231_);
return v_res_1238_;
}
}
lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_st_ref_get(v___y_1240_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT void l_Lean_MVarId_getNondepPropHyps___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_1239_ = stack[0].m_obj;
lean_object* v___y_1240_ = stack[1].m_obj;
lean_object* v___y_1241_ = stack[2].m_obj;
lean_object* v___y_1242_ = stack[3].m_obj;
lean_object* v___y_1243_ = stack[4].m_obj;
lean_object* v___y_1244_ = stack[5].m_obj;
lean_object* v_res_1248_;
v_res_1248_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1248_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
return v_res_1256_;
}
}
lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_visited_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; lean_object* v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1260_ = lean_st_ref_get(v_a_1258_);
v_visited_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_visited_1261_);
lean_dec(v___x_1260_);
v___x_1262_ = lean_ptr_addr(v_e_1257_);
v___x_1263_ = ((size_t)8191ULL);
v___x_1264_ = lean_usize_mod(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_array_uget(v_visited_1261_, v___x_1264_);
lean_dec_ref(v_visited_1261_);
v___x_1266_ = lean_ptr_addr(v___x_1265_);
lean_dec(v___x_1265_);
v___x_1267_ = lean_usize_dec_eq(v___x_1266_, v___x_1262_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v_visited_1269_; lean_object* v_checked_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1281_; 
v___x_1268_ = lean_st_ref_take(v_a_1258_);
v_visited_1269_ = lean_ctor_get(v___x_1268_, 0);
v_checked_1270_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1281_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_checked_1270_);
lean_inc(v_visited_1269_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1281_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_array_uset(v_visited_1269_, v___x_1264_, v_e_1257_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_checked_1270_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_st_ref_put(v_a_1258_, v___x_1276_);
v___x_1278_ = lean_box(v___x_1267_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref(v_e_1257_);
v___x_1282_ = lean_box(v___x_1267_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1257_ = stack[0].m_obj;
lean_object* v_a_1258_ = stack[1].m_obj;
lean_object* v_res_1284_;
v_res_1284_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1257_, v_a_1258_);
stack->m_obj
 = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1285_, lean_object* v_a_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1285_, v_a_1286_);
lean_dec(v_a_1286_);
return v_res_1288_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1289_, lean_object* v_x_1290_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
return v___x_1291_;
}
else
{
lean_object* v_key_1292_; lean_object* v_tail_1293_; uint8_t v___x_1294_; 
v_key_1292_ = lean_ctor_get(v_x_1290_, 0);
v_tail_1293_ = lean_ctor_get(v_x_1290_, 2);
v___x_1294_ = lean_expr_eqv(v_key_1292_, v_a_1289_);
if (v___x_1294_ == 0)
{
v_x_1290_ = v_tail_1293_;
goto _start;
}
else
{
return v___x_1294_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1289_ = stack[0].m_obj;
lean_object* v_x_1290_ = stack[1].m_obj;
uint8_t v_res_1296_;
v_res_1296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1289_, v_x_1290_);
stack->m_num = v_res_1296_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec_ref(v_a_1297_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
return v_x_1301_;
}
else
{
lean_object* v_key_1303_; lean_object* v_value_1304_; lean_object* v_tail_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1328_; 
v_key_1303_ = lean_ctor_get(v_x_1302_, 0);
v_value_1304_ = lean_ctor_get(v_x_1302_, 1);
v_tail_1305_ = lean_ctor_get(v_x_1302_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_x_1302_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1307_ = v_x_1302_;
v_isShared_1308_ = v_isSharedCheck_1328_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_tail_1305_);
lean_inc(v_value_1304_);
lean_inc(v_key_1303_);
lean_dec(v_x_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1328_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v_fold_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1309_ = lean_array_get_size(v_x_1301_);
v___x_1310_ = l_Lean_Expr_hash(v_key_1303_);
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
v___x_1322_ = lean_array_uget_borrowed(v_x_1301_, v___x_1321_);
lean_inc(v___x_1322_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 2, v___x_1322_);
v___x_1324_ = v___x_1307_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_key_1303_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_value_1304_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_array_uset(v_x_1301_, v___x_1321_, v___x_1324_);
v_x_1301_ = v___x_1325_;
v_x_1302_ = v_tail_1305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1329_, lean_object* v_source_1330_, lean_object* v_target_1331_){
_start:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_array_get_size(v_source_1330_);
v___x_1333_ = lean_nat_dec_lt(v_i_1329_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v_source_1330_);
lean_dec(v_i_1329_);
return v_target_1331_;
}
else
{
lean_object* v_es_1334_; lean_object* v___x_1335_; lean_object* v_source_1336_; lean_object* v_target_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_es_1334_ = lean_array_fget(v_source_1330_, v_i_1329_);
v___x_1335_ = lean_box(0);
v_source_1336_ = lean_array_fset(v_source_1330_, v_i_1329_, v___x_1335_);
v_target_1337_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1331_, v_es_1334_);
v___x_1338_ = lean_unsigned_to_nat(1u);
v___x_1339_ = lean_nat_add(v_i_1329_, v___x_1338_);
lean_dec(v_i_1329_);
v_i_1329_ = v___x_1339_;
v_source_1330_ = v_source_1336_;
v_target_1331_ = v_target_1337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_nbuckets_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1342_ = lean_array_get_size(v_data_1341_);
v___x_1343_ = lean_unsigned_to_nat(2u);
v_nbuckets_1344_ = lean_nat_mul(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_mk_array(v_nbuckets_1344_, v___x_1346_);
v___x_1348_ = lean_array_propagate_mark(v_data_1341_, v___x_1347_);
v___x_1349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1345_, v_data_1341_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1350_, lean_object* v_a_1351_, lean_object* v_b_1352_){
_start:
{
lean_object* v_size_1353_; lean_object* v_buckets_1354_; lean_object* v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v_fold_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; lean_object* v_bkt_1368_; uint8_t v___x_1369_; 
v_size_1353_ = lean_ctor_get(v_m_1350_, 0);
v_buckets_1354_ = lean_ctor_get(v_m_1350_, 1);
v___x_1355_ = lean_array_get_size(v_buckets_1354_);
v___x_1356_ = l_Lean_Expr_hash(v_a_1351_);
v___x_1357_ = 32ULL;
v___x_1358_ = lean_uint64_shift_right(v___x_1356_, v___x_1357_);
v_fold_1359_ = lean_uint64_xor(v___x_1356_, v___x_1358_);
v___x_1360_ = 16ULL;
v___x_1361_ = lean_uint64_shift_right(v_fold_1359_, v___x_1360_);
v___x_1362_ = lean_uint64_xor(v_fold_1359_, v___x_1361_);
v___x_1363_ = lean_uint64_to_usize(v___x_1362_);
v___x_1364_ = lean_usize_of_nat(v___x_1355_);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_sub(v___x_1364_, v___x_1365_);
v___x_1367_ = lean_usize_land(v___x_1363_, v___x_1366_);
v_bkt_1368_ = lean_array_uget_borrowed(v_buckets_1354_, v___x_1367_);
v___x_1369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1351_, v_bkt_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1390_; 
lean_inc_ref(v_buckets_1354_);
lean_inc(v_size_1353_);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_m_1350_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; 
v_unused_1391_ = lean_ctor_get(v_m_1350_, 1);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_m_1350_, 0);
lean_dec(v_unused_1392_);
v___x_1371_ = v_m_1350_;
v_isShared_1372_ = v_isSharedCheck_1390_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_m_1350_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1390_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v_size_x27_1374_; lean_object* v___x_1375_; lean_object* v_buckets_x27_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1373_ = lean_unsigned_to_nat(1u);
v_size_x27_1374_ = lean_nat_add(v_size_1353_, v___x_1373_);
lean_dec(v_size_1353_);
lean_inc(v_bkt_1368_);
v___x_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1351_);
lean_ctor_set(v___x_1375_, 1, v_b_1352_);
lean_ctor_set(v___x_1375_, 2, v_bkt_1368_);
v_buckets_x27_1376_ = lean_array_uset(v_buckets_1354_, v___x_1367_, v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(4u);
v___x_1378_ = lean_nat_mul(v_size_x27_1374_, v___x_1377_);
v___x_1379_ = lean_unsigned_to_nat(3u);
v___x_1380_ = lean_nat_div(v___x_1378_, v___x_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_array_get_size(v_buckets_x27_1376_);
v___x_1382_ = lean_nat_dec_le(v___x_1380_, v___x_1381_);
lean_dec(v___x_1380_);
if (v___x_1382_ == 0)
{
lean_object* v_val_1383_; lean_object* v___x_1385_; 
v_val_1383_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1376_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_val_1383_);
lean_ctor_set(v___x_1371_, 0, v_size_x27_1374_);
v___x_1385_ = v___x_1371_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_size_x27_1374_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_val_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
else
{
lean_object* v___x_1388_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_buckets_x27_1376_);
lean_ctor_set(v___x_1371_, 0, v_size_x27_1374_);
v___x_1388_ = v___x_1371_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_size_x27_1374_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_buckets_x27_1376_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_dec(v_b_1352_);
lean_dec_ref(v_a_1351_);
return v_m_1350_;
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_buckets_1395_; lean_object* v___x_1396_; uint64_t v___x_1397_; uint64_t v___x_1398_; uint64_t v___x_1399_; uint64_t v_fold_1400_; uint64_t v___x_1401_; uint64_t v___x_1402_; uint64_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_buckets_1395_ = lean_ctor_get(v_m_1393_, 1);
v___x_1396_ = lean_array_get_size(v_buckets_1395_);
v___x_1397_ = l_Lean_Expr_hash(v_a_1394_);
v___x_1398_ = 32ULL;
v___x_1399_ = lean_uint64_shift_right(v___x_1397_, v___x_1398_);
v_fold_1400_ = lean_uint64_xor(v___x_1397_, v___x_1399_);
v___x_1401_ = 16ULL;
v___x_1402_ = lean_uint64_shift_right(v_fold_1400_, v___x_1401_);
v___x_1403_ = lean_uint64_xor(v_fold_1400_, v___x_1402_);
v___x_1404_ = lean_uint64_to_usize(v___x_1403_);
v___x_1405_ = lean_usize_of_nat(v___x_1396_);
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_sub(v___x_1405_, v___x_1406_);
v___x_1408_ = lean_usize_land(v___x_1404_, v___x_1407_);
v___x_1409_ = lean_array_uget_borrowed(v_buckets_1395_, v___x_1408_);
v___x_1410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1394_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1393_ = stack[0].m_obj;
lean_object* v_a_1394_ = stack[1].m_obj;
uint8_t v_res_1411_;
v_res_1411_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1393_, v_a_1394_);
stack->m_num = v_res_1411_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1412_, lean_object* v_a_1413_){
_start:
{
uint8_t v_res_1414_; lean_object* v_r_1415_; 
v_res_1414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1412_, v_a_1413_);
lean_dec_ref(v_a_1413_);
lean_dec_ref(v_m_1412_);
v_r_1415_ = lean_box(v_res_1414_);
return v_r_1415_;
}
}
lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v_checked_1420_; uint8_t v___x_1421_; 
v___x_1419_ = lean_st_ref_get(v_a_1417_);
v_checked_1420_ = lean_ctor_get(v___x_1419_, 1);
lean_inc_ref(v_checked_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1420_, v_e_1416_);
lean_dec_ref(v_checked_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v_visited_1423_; lean_object* v_checked_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1436_; 
v___x_1422_ = lean_st_ref_take(v_a_1417_);
v_visited_1423_ = lean_ctor_get(v___x_1422_, 0);
v_checked_1424_ = lean_ctor_get(v___x_1422_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1426_ = v___x_1422_;
v_isShared_1427_ = v_isSharedCheck_1436_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_checked_1424_);
lean_inc(v_visited_1423_);
lean_dec(v___x_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1436_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1424_, v_e_1416_, v___x_1428_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1429_);
v___x_1431_ = v___x_1426_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_visited_1423_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_st_ref_put(v_a_1417_, v___x_1431_);
v___x_1433_ = lean_box(v___x_1421_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_e_1416_);
v___x_1437_ = lean_box(v___x_1421_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1416_ = stack[0].m_obj;
lean_object* v_a_1417_ = stack[1].m_obj;
lean_object* v_res_1439_;
v_res_1439_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1416_, v_a_1417_);
stack->m_obj
 = v_res_1439_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1440_, lean_object* v_a_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1440_, v_a_1441_);
lean_dec(v_a_1441_);
return v_res_1443_;
}
}
lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1444_, lean_object* v_f_1445_, uint8_t v_stopWhenVisited_1446_, lean_object* v_e_1447_, lean_object* v_a_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v_d_1461_; lean_object* v_b_1462_; lean_object* v___y_1463_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___x_1493_; 
lean_inc_ref(v_e_1447_);
v___x_1493_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1526_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1526_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1526_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_unbox(v_a_1494_);
lean_dec(v_a_1494_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
lean_del_object(v___x_1496_);
lean_inc_ref(v_p_1444_);
lean_inc_ref(v_e_1447_);
v___x_1499_ = lean_apply_1(v_p_1444_, v_e_1447_);
v___x_1500_ = lean_unbox(v___x_1499_);
if (v___x_1500_ == 0)
{
v___y_1467_ = v_a_1448_;
v___y_1468_ = v___y_1449_;
v___y_1469_ = v___y_1450_;
v___y_1470_ = v___y_1451_;
v___y_1471_ = v___y_1452_;
v___y_1472_ = v___y_1453_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1501_; 
lean_inc_ref(v_e_1447_);
v___x_1501_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; uint8_t v___x_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = lean_unbox(v_a_1502_);
lean_dec(v_a_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_inc_ref(v_f_1445_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
lean_inc_ref(v_e_1447_);
v___x_1504_ = lean_apply_7(v_f_1445_, v_e_1447_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, lean_box(0));
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1512_; 
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v___x_1504_, 0);
lean_dec(v_unused_1513_);
v___x_1506_ = v___x_1504_;
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v___x_1504_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1512_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
if (v_stopWhenVisited_1446_ == 0)
{
lean_del_object(v___x_1506_);
v___y_1467_ = v_a_1448_;
v___y_1468_ = v___y_1449_;
v___y_1469_ = v___y_1450_;
v___y_1470_ = v___y_1451_;
v___y_1471_ = v___y_1452_;
v___y_1472_ = v___y_1453_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_dec_ref(v_e_1447_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
v___x_1508_ = lean_box(0);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1508_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
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
lean_dec_ref(v_e_1447_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
return v___x_1504_;
}
}
else
{
v___y_1467_ = v_a_1448_;
v___y_1468_ = v___y_1449_;
v___y_1469_ = v___y_1450_;
v___y_1470_ = v___y_1451_;
v___y_1471_ = v___y_1452_;
v___y_1472_ = v___y_1453_;
goto v___jp_1466_;
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_e_1447_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
v_a_1514_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1501_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1501_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec_ref(v_e_1447_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
v___x_1522_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1522_);
v___x_1524_ = v___x_1496_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_e_1447_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
v_a_1527_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1493_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1493_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
v___jp_1455_:
{
lean_object* v___x_1464_; 
lean_inc_ref(v_f_1445_);
lean_inc_ref(v_p_1444_);
v___x_1464_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1444_, v_f_1445_, v_stopWhenVisited_1446_, v_d_1461_, v___y_1463_, v___y_1457_, v___y_1456_, v___y_1458_, v___y_1460_, v___y_1459_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_dec_ref_known(v___x_1464_, 1);
v_e_1447_ = v_b_1462_;
v_a_1448_ = v___y_1463_;
v___y_1449_ = v___y_1457_;
v___y_1450_ = v___y_1456_;
v___y_1451_ = v___y_1458_;
v___y_1452_ = v___y_1460_;
v___y_1453_ = v___y_1459_;
goto _start;
}
else
{
lean_dec_ref(v_b_1462_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
return v___x_1464_;
}
}
v___jp_1466_:
{
switch(lean_obj_tag(v_e_1447_))
{
case 7:
{
lean_object* v_binderType_1473_; lean_object* v_body_1474_; 
v_binderType_1473_ = lean_ctor_get(v_e_1447_, 1);
lean_inc_ref(v_binderType_1473_);
v_body_1474_ = lean_ctor_get(v_e_1447_, 2);
lean_inc_ref(v_body_1474_);
lean_dec_ref_known(v_e_1447_, 3);
v___y_1456_ = v___y_1469_;
v___y_1457_ = v___y_1468_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v___y_1472_;
v___y_1460_ = v___y_1471_;
v_d_1461_ = v_binderType_1473_;
v_b_1462_ = v_body_1474_;
v___y_1463_ = v___y_1467_;
goto v___jp_1455_;
}
case 6:
{
lean_object* v_binderType_1475_; lean_object* v_body_1476_; 
v_binderType_1475_ = lean_ctor_get(v_e_1447_, 1);
lean_inc_ref(v_binderType_1475_);
v_body_1476_ = lean_ctor_get(v_e_1447_, 2);
lean_inc_ref(v_body_1476_);
lean_dec_ref_known(v_e_1447_, 3);
v___y_1456_ = v___y_1469_;
v___y_1457_ = v___y_1468_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v___y_1472_;
v___y_1460_ = v___y_1471_;
v_d_1461_ = v_binderType_1475_;
v_b_1462_ = v_body_1476_;
v___y_1463_ = v___y_1467_;
goto v___jp_1455_;
}
case 8:
{
lean_object* v_type_1477_; lean_object* v_value_1478_; lean_object* v_body_1479_; lean_object* v___x_1480_; 
v_type_1477_ = lean_ctor_get(v_e_1447_, 1);
lean_inc_ref(v_type_1477_);
v_value_1478_ = lean_ctor_get(v_e_1447_, 2);
lean_inc_ref(v_value_1478_);
v_body_1479_ = lean_ctor_get(v_e_1447_, 3);
lean_inc_ref(v_body_1479_);
lean_dec_ref_known(v_e_1447_, 4);
lean_inc_ref(v_f_1445_);
lean_inc_ref(v_p_1444_);
v___x_1480_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1444_, v_f_1445_, v_stopWhenVisited_1446_, v_type_1477_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1481_; 
lean_dec_ref_known(v___x_1480_, 1);
lean_inc_ref(v_f_1445_);
lean_inc_ref(v_p_1444_);
v___x_1481_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1444_, v_f_1445_, v_stopWhenVisited_1446_, v_value_1478_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_dec_ref_known(v___x_1481_, 1);
v_e_1447_ = v_body_1479_;
v_a_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v___y_1470_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v___y_1472_;
goto _start;
}
else
{
lean_dec_ref(v_body_1479_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
return v___x_1481_;
}
}
else
{
lean_dec_ref(v_body_1479_);
lean_dec_ref(v_value_1478_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
return v___x_1480_;
}
}
case 5:
{
lean_object* v_fn_1483_; lean_object* v_arg_1484_; lean_object* v___x_1485_; 
v_fn_1483_ = lean_ctor_get(v_e_1447_, 0);
lean_inc_ref(v_fn_1483_);
v_arg_1484_ = lean_ctor_get(v_e_1447_, 1);
lean_inc_ref(v_arg_1484_);
lean_dec_ref_known(v_e_1447_, 2);
lean_inc_ref(v_f_1445_);
lean_inc_ref(v_p_1444_);
v___x_1485_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1444_, v_f_1445_, v_stopWhenVisited_1446_, v_fn_1483_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
v_e_1447_ = v_arg_1484_;
v_a_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v___y_1470_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v___y_1472_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1484_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
return v___x_1485_;
}
}
case 10:
{
lean_object* v_expr_1487_; 
v_expr_1487_ = lean_ctor_get(v_e_1447_, 1);
lean_inc_ref(v_expr_1487_);
lean_dec_ref_known(v_e_1447_, 2);
v_e_1447_ = v_expr_1487_;
v_a_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v___y_1470_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v___y_1472_;
goto _start;
}
case 11:
{
lean_object* v_struct_1489_; 
v_struct_1489_ = lean_ctor_get(v_e_1447_, 2);
lean_inc_ref(v_struct_1489_);
lean_dec_ref_known(v_e_1447_, 3);
v_e_1447_ = v_struct_1489_;
v_a_1448_ = v___y_1467_;
v___y_1449_ = v___y_1468_;
v___y_1450_ = v___y_1469_;
v___y_1451_ = v___y_1470_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v___y_1472_;
goto _start;
}
default: 
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec_ref(v_e_1447_);
lean_dec_ref(v_f_1445_);
lean_dec_ref(v_p_1444_);
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1444_ = stack[0].m_obj;
lean_object* v_f_1445_ = stack[1].m_obj;
uint8_t v_stopWhenVisited_1446_ = stack[2].m_num;
lean_object* v_e_1447_ = stack[3].m_obj;
lean_object* v_a_1448_ = stack[4].m_obj;
lean_object* v___y_1449_ = stack[5].m_obj;
lean_object* v___y_1450_ = stack[6].m_obj;
lean_object* v___y_1451_ = stack[7].m_obj;
lean_object* v___y_1452_ = stack[8].m_obj;
lean_object* v___y_1453_ = stack[9].m_obj;
lean_object* v_res_1535_;
v_res_1535_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1444_, v_f_1445_, v_stopWhenVisited_1446_, v_e_1447_, v_a_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
stack->m_obj
 = v_res_1535_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1536_, lean_object* v_f_1537_, lean_object* v_stopWhenVisited_1538_, lean_object* v_e_1539_, lean_object* v_a_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1547_; lean_object* v_res_1548_; 
v_stopWhenVisited_boxed_1547_ = lean_unbox(v_stopWhenVisited_1538_);
v_res_1548_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1536_, v_f_1537_, v_stopWhenVisited_boxed_1547_, v_e_1539_, v_a_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec(v_a_1540_);
return v_res_1548_;
}
}
lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1549_, lean_object* v_f_1550_, lean_object* v_e_1551_, uint8_t v_stopWhenVisited_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = l_Lean_ForEachExprWhere_initCache;
v___x_1560_ = lean_st_mk_ref(v___x_1559_);
v___x_1561_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1549_, v_f_1550_, v_stopWhenVisited_1552_, v_e_1551_, v___x_1560_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1570_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = lean_st_ref_get(v___x_1560_);
lean_dec(v___x_1560_);
lean_dec(v___x_1566_);
if (v_isShared_1565_ == 0)
{
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1562_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_dec(v___x_1560_);
return v___x_1561_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1549_ = stack[0].m_obj;
lean_object* v_f_1550_ = stack[1].m_obj;
lean_object* v_e_1551_ = stack[2].m_obj;
uint8_t v_stopWhenVisited_1552_ = stack[3].m_num;
lean_object* v___y_1553_ = stack[4].m_obj;
lean_object* v___y_1554_ = stack[5].m_obj;
lean_object* v___y_1555_ = stack[6].m_obj;
lean_object* v___y_1556_ = stack[7].m_obj;
lean_object* v___y_1557_ = stack[8].m_obj;
lean_object* v_res_1571_;
v_res_1571_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1549_, v_f_1550_, v_e_1551_, v_stopWhenVisited_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
stack->m_obj
 = v_res_1571_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1572_, lean_object* v_f_1573_, lean_object* v_e_1574_, lean_object* v_stopWhenVisited_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1582_; lean_object* v_res_1583_; 
v_stopWhenVisited_boxed_1582_ = lean_unbox(v_stopWhenVisited_1575_);
v_res_1583_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1572_, v_f_1573_, v_e_1574_, v_stopWhenVisited_boxed_1582_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
return v_res_1583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1585_, lean_object* v___f_1586_, uint8_t v___x_1587_, lean_object* v_e_1588_, lean_object* v_candidates_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1588_, v___y_1591_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___y_1600_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = l_Lean_Expr_hasFVar(v_a_1596_);
v___x_1598_ = lean_st_mk_ref(v_candidates_1589_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v_a_1596_);
lean_dec_ref(v___f_1586_);
v___x_1610_ = lean_box(0);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___x_1598_);
v___x_1611_ = lean_apply_7(v___f_1585_, v___x_1610_, v___x_1598_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, lean_box(0));
v___y_1600_ = v___x_1611_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1613_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1612_, v___f_1586_, v_a_1596_, v___x_1587_, v___x_1598_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___x_1598_);
v___x_1615_ = lean_apply_7(v___f_1585_, v_a_1614_, v___x_1598_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, lean_box(0));
v___y_1600_ = v___x_1615_;
goto v___jp_1599_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v___x_1598_);
lean_dec_ref(v___f_1585_);
v_a_1616_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1613_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1613_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
v___jp_1599_:
{
if (lean_obj_tag(v___y_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_a_1601_ = lean_ctor_get(v___y_1600_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___y_1600_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1603_ = v___y_1600_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___y_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_st_ref_get(v___x_1598_);
lean_dec(v___x_1598_);
lean_dec(v___x_1605_);
if (v_isShared_1604_ == 0)
{
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1601_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_dec(v___x_1598_);
return v___y_1600_;
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_candidates_1589_);
lean_dec_ref(v___f_1586_);
lean_dec_ref(v___f_1585_);
v_a_1624_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1595_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1595_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1585_ = stack[0].m_obj;
lean_object* v___f_1586_ = stack[1].m_obj;
uint8_t v___x_1587_ = stack[2].m_num;
lean_object* v_e_1588_ = stack[3].m_obj;
lean_object* v_candidates_1589_ = stack[4].m_obj;
lean_object* v___y_1590_ = stack[5].m_obj;
lean_object* v___y_1591_ = stack[6].m_obj;
lean_object* v___y_1592_ = stack[7].m_obj;
lean_object* v___y_1593_ = stack[8].m_obj;
lean_object* v_res_1632_;
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1585_, v___f_1586_, v___x_1587_, v_e_1588_, v_candidates_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
stack->m_obj
 = v_res_1632_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1633_, lean_object* v___f_1634_, lean_object* v___x_1635_, lean_object* v_e_1636_, lean_object* v_candidates_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
uint8_t v___x_17253__boxed_1643_; lean_object* v_res_1644_; 
v___x_17253__boxed_1643_ = lean_unbox(v___x_1635_);
v_res_1644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1633_, v___f_1634_, v___x_17253__boxed_1643_, v_e_1636_, v_candidates_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1644_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_____r_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_st_ref_get(v___y_1646_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_1645_ = stack[0].m_obj;
lean_object* v___y_1646_ = stack[1].m_obj;
lean_object* v___y_1647_ = stack[2].m_obj;
lean_object* v___y_1648_ = stack[3].m_obj;
lean_object* v___y_1649_ = stack[4].m_obj;
lean_object* v___y_1650_ = stack[5].m_obj;
lean_object* v_res_1654_;
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_____r_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
return v_res_1662_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_e_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1670_ = lean_st_ref_take(v___y_1664_);
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Lean_Expr_fvarId_x21(v_e_1663_);
v___x_1673_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1670_, v___x_1672_);
lean_dec(v___x_1672_);
v___x_1674_ = lean_st_ref_put(v___y_1664_, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1671_);
return v___x_1675_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1663_ = stack[0].m_obj;
lean_object* v___y_1664_ = stack[1].m_obj;
lean_object* v___y_1665_ = stack[2].m_obj;
lean_object* v___y_1666_ = stack[3].m_obj;
lean_object* v___y_1667_ = stack[4].m_obj;
lean_object* v___y_1668_ = stack[5].m_obj;
lean_object* v_res_1676_;
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
stack->m_obj
 = v_res_1676_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_e_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v_e_1677_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1685_, lean_object* v_x_1686_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 0)
{
return v_x_1685_;
}
else
{
lean_object* v_key_1687_; lean_object* v_value_1688_; lean_object* v_tail_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1712_; 
v_key_1687_ = lean_ctor_get(v_x_1686_, 0);
v_value_1688_ = lean_ctor_get(v_x_1686_, 1);
v_tail_1689_ = lean_ctor_get(v_x_1686_, 2);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1686_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1691_ = v_x_1686_;
v_isShared_1692_ = v_isSharedCheck_1712_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_tail_1689_);
lean_inc(v_value_1688_);
lean_inc(v_key_1687_);
lean_dec(v_x_1686_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1712_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; uint64_t v___x_1696_; uint64_t v_fold_1697_; uint64_t v___x_1698_; uint64_t v___x_1699_; uint64_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1693_ = lean_array_get_size(v_x_1685_);
v___x_1694_ = l_Lean_instHashableFVarId_hash(v_key_1687_);
v___x_1695_ = 32ULL;
v___x_1696_ = lean_uint64_shift_right(v___x_1694_, v___x_1695_);
v_fold_1697_ = lean_uint64_xor(v___x_1694_, v___x_1696_);
v___x_1698_ = 16ULL;
v___x_1699_ = lean_uint64_shift_right(v_fold_1697_, v___x_1698_);
v___x_1700_ = lean_uint64_xor(v_fold_1697_, v___x_1699_);
v___x_1701_ = lean_uint64_to_usize(v___x_1700_);
v___x_1702_ = lean_usize_of_nat(v___x_1693_);
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = lean_usize_sub(v___x_1702_, v___x_1703_);
v___x_1705_ = lean_usize_land(v___x_1701_, v___x_1704_);
v___x_1706_ = lean_array_uget_borrowed(v_x_1685_, v___x_1705_);
lean_inc(v___x_1706_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 2, v___x_1706_);
v___x_1708_ = v___x_1691_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_key_1687_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_value_1688_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_array_uset(v_x_1685_, v___x_1705_, v___x_1708_);
v_x_1685_ = v___x_1709_;
v_x_1686_ = v_tail_1689_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1713_, lean_object* v_source_1714_, lean_object* v_target_1715_){
_start:
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = lean_array_get_size(v_source_1714_);
v___x_1717_ = lean_nat_dec_lt(v_i_1713_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec_ref(v_source_1714_);
lean_dec(v_i_1713_);
return v_target_1715_;
}
else
{
lean_object* v_es_1718_; lean_object* v___x_1719_; lean_object* v_source_1720_; lean_object* v_target_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_es_1718_ = lean_array_fget(v_source_1714_, v_i_1713_);
v___x_1719_ = lean_box(0);
v_source_1720_ = lean_array_fset(v_source_1714_, v_i_1713_, v___x_1719_);
v_target_1721_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1715_, v_es_1718_);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_add(v_i_1713_, v___x_1722_);
lean_dec(v_i_1713_);
v_i_1713_ = v___x_1723_;
v_source_1714_ = v_source_1720_;
v_target_1715_ = v_target_1721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v_nbuckets_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1726_ = lean_array_get_size(v_data_1725_);
v___x_1727_ = lean_unsigned_to_nat(2u);
v_nbuckets_1728_ = lean_nat_mul(v___x_1726_, v___x_1727_);
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_mk_array(v_nbuckets_1728_, v___x_1730_);
v___x_1732_ = lean_array_propagate_mark(v_data_1725_, v___x_1731_);
v___x_1733_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1729_, v_data_1725_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1734_, lean_object* v_a_1735_, lean_object* v_b_1736_){
_start:
{
lean_object* v_size_1737_; lean_object* v_buckets_1738_; lean_object* v___x_1739_; uint64_t v___x_1740_; uint64_t v___x_1741_; uint64_t v___x_1742_; uint64_t v_fold_1743_; uint64_t v___x_1744_; uint64_t v___x_1745_; uint64_t v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v_bkt_1752_; uint8_t v___x_1753_; 
v_size_1737_ = lean_ctor_get(v_m_1734_, 0);
v_buckets_1738_ = lean_ctor_get(v_m_1734_, 1);
v___x_1739_ = lean_array_get_size(v_buckets_1738_);
v___x_1740_ = l_Lean_instHashableFVarId_hash(v_a_1735_);
v___x_1741_ = 32ULL;
v___x_1742_ = lean_uint64_shift_right(v___x_1740_, v___x_1741_);
v_fold_1743_ = lean_uint64_xor(v___x_1740_, v___x_1742_);
v___x_1744_ = 16ULL;
v___x_1745_ = lean_uint64_shift_right(v_fold_1743_, v___x_1744_);
v___x_1746_ = lean_uint64_xor(v_fold_1743_, v___x_1745_);
v___x_1747_ = lean_uint64_to_usize(v___x_1746_);
v___x_1748_ = lean_usize_of_nat(v___x_1739_);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_sub(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_usize_land(v___x_1747_, v___x_1750_);
v_bkt_1752_ = lean_array_uget_borrowed(v_buckets_1738_, v___x_1751_);
v___x_1753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1735_, v_bkt_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1774_; 
lean_inc_ref(v_buckets_1738_);
lean_inc(v_size_1737_);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_m_1734_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1775_ = lean_ctor_get(v_m_1734_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_m_1734_, 0);
lean_dec(v_unused_1776_);
v___x_1755_ = v_m_1734_;
v_isShared_1756_ = v_isSharedCheck_1774_;
goto v_resetjp_1754_;
}
else
{
lean_dec(v_m_1734_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1774_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v_size_x27_1758_; lean_object* v___x_1759_; lean_object* v_buckets_x27_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1757_ = lean_unsigned_to_nat(1u);
v_size_x27_1758_ = lean_nat_add(v_size_1737_, v___x_1757_);
lean_dec(v_size_1737_);
lean_inc(v_bkt_1752_);
v___x_1759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1759_, 0, v_a_1735_);
lean_ctor_set(v___x_1759_, 1, v_b_1736_);
lean_ctor_set(v___x_1759_, 2, v_bkt_1752_);
v_buckets_x27_1760_ = lean_array_uset(v_buckets_1738_, v___x_1751_, v___x_1759_);
v___x_1761_ = lean_unsigned_to_nat(4u);
v___x_1762_ = lean_nat_mul(v_size_x27_1758_, v___x_1761_);
v___x_1763_ = lean_unsigned_to_nat(3u);
v___x_1764_ = lean_nat_div(v___x_1762_, v___x_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_array_get_size(v_buckets_x27_1760_);
v___x_1766_ = lean_nat_dec_le(v___x_1764_, v___x_1765_);
lean_dec(v___x_1764_);
if (v___x_1766_ == 0)
{
lean_object* v_val_1767_; lean_object* v___x_1769_; 
v_val_1767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1760_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v_val_1767_);
lean_ctor_set(v___x_1755_, 0, v_size_x27_1758_);
v___x_1769_ = v___x_1755_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_size_x27_1758_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_val_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
else
{
lean_object* v___x_1772_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v_buckets_x27_1760_);
lean_ctor_set(v___x_1755_, 0, v_size_x27_1758_);
v___x_1772_ = v___x_1755_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_size_x27_1758_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_buckets_x27_1760_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_dec(v_b_1736_);
lean_dec(v_a_1735_);
return v_m_1734_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1779_, size_t v_sz_1780_, size_t v_i_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_usize_dec_lt(v_i_1781_, v_sz_1780_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_b_1782_);
return v___x_1789_;
}
else
{
lean_object* v_snd_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1857_; 
v_snd_1790_ = lean_ctor_get(v_b_1782_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_b_1782_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v_b_1782_, 0);
lean_dec(v_unused_1858_);
v___x_1792_ = v_b_1782_;
v_isShared_1793_ = v_isSharedCheck_1857_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_snd_1790_);
lean_dec(v_b_1782_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1857_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v_a_1796_; lean_object* v_a_1803_; 
v___x_1794_ = lean_box(0);
v_a_1803_ = lean_array_uget_borrowed(v_as_1779_, v_i_1781_);
if (lean_obj_tag(v_a_1803_) == 0)
{
v_a_1796_ = v_snd_1790_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1804_; lean_object* v___y_1806_; lean_object* v___y_1811_; uint8_t v___y_1812_; uint8_t v___x_1813_; 
v_val_1804_ = lean_ctor_get(v_a_1803_, 0);
v___x_1813_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1804_);
if (v___x_1813_ == 0)
{
lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v_candidates_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___x_1835_; 
v___f_1814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1816_ = l_Lean_LocalDecl_type(v_val_1804_);
lean_inc_ref(v___x_1816_);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1814_, v___f_1815_, v___x_1813_, v___x_1816_, v_snd_1790_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l_Lean_LocalDecl_value_x3f(v_val_1804_, v___x_1813_);
if (lean_obj_tag(v___x_1837_) == 0)
{
v_candidates_1818_ = v_a_1836_;
v___y_1819_ = v___y_1783_;
v___y_1820_ = v___y_1784_;
v___y_1821_ = v___y_1785_;
v___y_1822_ = v___y_1786_;
goto v___jp_1817_;
}
else
{
lean_object* v_val_1838_; lean_object* v___x_1839_; 
v_val_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1814_, v___f_1815_, v___x_1813_, v_val_1838_, v_a_1836_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v_candidates_1818_ = v_a_1840_;
v___y_1819_ = v___y_1783_;
v___y_1820_ = v___y_1784_;
v___y_1821_ = v___y_1785_;
v___y_1822_ = v___y_1786_;
goto v___jp_1817_;
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___x_1816_);
lean_del_object(v___x_1792_);
v_a_1841_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1839_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v___x_1816_);
lean_del_object(v___x_1792_);
v_a_1849_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1835_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1835_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
v___jp_1817_:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_Meta_isProp(v___x_1816_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; uint8_t v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = lean_unbox(v_a_1824_);
lean_dec(v_a_1824_);
if (v___x_1825_ == 0)
{
v___y_1811_ = v_candidates_1818_;
v___y_1812_ = v___x_1813_;
goto v___jp_1810_;
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Lean_LocalDecl_hasValue(v_val_1804_, v___x_1813_);
if (v___x_1826_ == 0)
{
v___y_1806_ = v_candidates_1818_;
goto v___jp_1805_;
}
else
{
v___y_1811_ = v_candidates_1818_;
v___y_1812_ = v___x_1813_;
goto v___jp_1810_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_candidates_1818_);
lean_del_object(v___x_1792_);
v_a_1827_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1823_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
else
{
v_a_1796_ = v_snd_1790_;
goto v___jp_1795_;
}
v___jp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = l_Lean_LocalDecl_fvarId(v_val_1804_);
v___x_1808_ = lean_box(0);
v___x_1809_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1806_, v___x_1807_, v___x_1808_);
v_a_1796_ = v___x_1809_;
goto v___jp_1795_;
}
v___jp_1810_:
{
if (v___y_1812_ == 0)
{
v_a_1796_ = v___y_1811_;
goto v___jp_1795_;
}
else
{
v___y_1806_ = v___y_1811_;
goto v___jp_1805_;
}
}
}
v___jp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v_a_1796_);
lean_ctor_set(v___x_1792_, 0, v___x_1794_);
v___x_1798_ = v___x_1792_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_a_1796_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1781_, v___x_1799_);
v_i_1781_ = v___x_1800_;
v_b_1782_ = v___x_1798_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1779_ = stack[0].m_obj;
size_t v_sz_1780_ = stack[1].m_num;
size_t v_i_1781_ = stack[2].m_num;
lean_object* v_b_1782_ = stack[3].m_obj;
lean_object* v___y_1783_ = stack[4].m_obj;
lean_object* v___y_1784_ = stack[5].m_obj;
lean_object* v___y_1785_ = stack[6].m_obj;
lean_object* v___y_1786_ = stack[7].m_obj;
lean_object* v_res_1859_;
v_res_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1779_, v_sz_1780_, v_i_1781_, v_b_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1860_, lean_object* v_sz_1861_, lean_object* v_i_1862_, lean_object* v_b_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
size_t v_sz_boxed_1869_; size_t v_i_boxed_1870_; lean_object* v_res_1871_; 
v_sz_boxed_1869_ = lean_unbox_usize(v_sz_1861_);
lean_dec(v_sz_1861_);
v_i_boxed_1870_ = lean_unbox_usize(v_i_1862_);
lean_dec(v_i_1862_);
v_res_1871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1860_, v_sz_boxed_1869_, v_i_boxed_1870_, v_b_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_as_1860_);
return v_res_1871_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1872_, size_t v_sz_1873_, size_t v_i_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_usize_dec_lt(v_i_1874_, v_sz_1873_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_b_1875_);
return v___x_1882_;
}
else
{
lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1950_; 
v_snd_1883_ = lean_ctor_get(v_b_1875_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_b_1875_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v_b_1875_, 0);
lean_dec(v_unused_1951_);
v___x_1885_ = v_b_1875_;
v_isShared_1886_ = v_isSharedCheck_1950_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_dec(v_b_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1950_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v_a_1889_; lean_object* v_a_1896_; 
v___x_1887_ = lean_box(0);
v_a_1896_ = lean_array_uget_borrowed(v_as_1872_, v_i_1874_);
if (lean_obj_tag(v_a_1896_) == 0)
{
v_a_1889_ = v_snd_1883_;
goto v___jp_1888_;
}
else
{
lean_object* v_val_1897_; lean_object* v___y_1899_; lean_object* v___y_1904_; uint8_t v___y_1905_; uint8_t v___x_1906_; 
v_val_1897_ = lean_ctor_get(v_a_1896_, 0);
v___x_1906_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1897_);
if (v___x_1906_ == 0)
{
lean_object* v___f_1907_; lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v_candidates_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___x_1928_; 
v___f_1907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1909_ = l_Lean_LocalDecl_type(v_val_1897_);
lean_inc_ref(v___x_1909_);
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1907_, v___f_1908_, v___x_1906_, v___x_1909_, v_snd_1883_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l_Lean_LocalDecl_value_x3f(v_val_1897_, v___x_1906_);
if (lean_obj_tag(v___x_1930_) == 0)
{
v_candidates_1911_ = v_a_1929_;
v___y_1912_ = v___y_1876_;
v___y_1913_ = v___y_1877_;
v___y_1914_ = v___y_1878_;
v___y_1915_ = v___y_1879_;
goto v___jp_1910_;
}
else
{
lean_object* v_val_1931_; lean_object* v___x_1932_; 
v_val_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1907_, v___f_1908_, v___x_1906_, v_val_1931_, v_a_1929_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_candidates_1911_ = v_a_1933_;
v___y_1912_ = v___y_1876_;
v___y_1913_ = v___y_1877_;
v___y_1914_ = v___y_1878_;
v___y_1915_ = v___y_1879_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1885_);
v_a_1934_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1932_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1932_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v___x_1909_);
lean_del_object(v___x_1885_);
v_a_1942_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1928_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1928_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
v___jp_1910_:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Meta_isProp(v___x_1909_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; uint8_t v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = lean_unbox(v_a_1917_);
lean_dec(v_a_1917_);
if (v___x_1918_ == 0)
{
v___y_1904_ = v_candidates_1911_;
v___y_1905_ = v___x_1906_;
goto v___jp_1903_;
}
else
{
uint8_t v___x_1919_; 
v___x_1919_ = l_Lean_LocalDecl_hasValue(v_val_1897_, v___x_1906_);
if (v___x_1919_ == 0)
{
v___y_1899_ = v_candidates_1911_;
goto v___jp_1898_;
}
else
{
v___y_1904_ = v_candidates_1911_;
v___y_1905_ = v___x_1906_;
goto v___jp_1903_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v_candidates_1911_);
lean_del_object(v___x_1885_);
v_a_1920_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1916_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
v_a_1889_ = v_snd_1883_;
goto v___jp_1888_;
}
v___jp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = l_Lean_LocalDecl_fvarId(v_val_1897_);
v___x_1901_ = lean_box(0);
v___x_1902_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1899_, v___x_1900_, v___x_1901_);
v_a_1889_ = v___x_1902_;
goto v___jp_1888_;
}
v___jp_1903_:
{
if (v___y_1905_ == 0)
{
v_a_1889_ = v___y_1904_;
goto v___jp_1888_;
}
else
{
v___y_1899_ = v___y_1904_;
goto v___jp_1898_;
}
}
}
v___jp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_a_1889_);
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1891_ = v___x_1885_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_a_1889_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
size_t v___x_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_add(v_i_1874_, v___x_1892_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1872_, v_sz_1873_, v___x_1893_, v___x_1891_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1872_ = stack[0].m_obj;
size_t v_sz_1873_ = stack[1].m_num;
size_t v_i_1874_ = stack[2].m_num;
lean_object* v_b_1875_ = stack[3].m_obj;
lean_object* v___y_1876_ = stack[4].m_obj;
lean_object* v___y_1877_ = stack[5].m_obj;
lean_object* v___y_1878_ = stack[6].m_obj;
lean_object* v___y_1879_ = stack[7].m_obj;
lean_object* v_res_1952_;
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1872_, v_sz_1873_, v_i_1874_, v_b_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
stack->m_obj
 = v_res_1952_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1953_, lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
size_t v_sz_boxed_1962_; size_t v_i_boxed_1963_; lean_object* v_res_1964_; 
v_sz_boxed_1962_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1963_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1953_, v_sz_boxed_1962_, v_i_boxed_1963_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec_ref(v_as_1953_);
return v_res_1964_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1965_, size_t v_sz_1966_, size_t v_i_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_lt(v_i_1967_, v_sz_1966_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_b_1968_);
return v___x_1975_;
}
else
{
lean_object* v_snd_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2043_; 
v_snd_1976_ = lean_ctor_get(v_b_1968_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_b_1968_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v_b_1968_, 0);
lean_dec(v_unused_2044_);
v___x_1978_ = v_b_1968_;
v_isShared_1979_ = v_isSharedCheck_2043_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_snd_1976_);
lean_dec(v_b_1968_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2043_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v_a_1982_; lean_object* v_a_1989_; 
v___x_1980_ = lean_box(0);
v_a_1989_ = lean_array_uget_borrowed(v_as_1965_, v_i_1967_);
if (lean_obj_tag(v_a_1989_) == 0)
{
v_a_1982_ = v_snd_1976_;
goto v___jp_1981_;
}
else
{
lean_object* v_val_1990_; lean_object* v___y_1992_; lean_object* v___y_1997_; uint8_t v___y_1998_; uint8_t v___x_1999_; 
v_val_1990_ = lean_ctor_get(v_a_1989_, 0);
v___x_1999_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1990_);
if (v___x_1999_ == 0)
{
lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; lean_object* v_candidates_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___x_2021_; 
v___f_2000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2002_ = l_Lean_LocalDecl_type(v_val_1990_);
lean_inc_ref(v___x_2002_);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2000_, v___f_2001_, v___x_1999_, v___x_2002_, v_snd_1976_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = l_Lean_LocalDecl_value_x3f(v_val_1990_, v___x_1999_);
if (lean_obj_tag(v___x_2023_) == 0)
{
v_candidates_2004_ = v_a_2022_;
v___y_2005_ = v___y_1969_;
v___y_2006_ = v___y_1970_;
v___y_2007_ = v___y_1971_;
v___y_2008_ = v___y_1972_;
goto v___jp_2003_;
}
else
{
lean_object* v_val_2024_; lean_object* v___x_2025_; 
v_val_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2000_, v___f_2001_, v___x_1999_, v_val_2024_, v_a_2022_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v_candidates_2004_ = v_a_2026_;
v___y_2005_ = v___y_1969_;
v___y_2006_ = v___y_1970_;
v___y_2007_ = v___y_1971_;
v___y_2008_ = v___y_1972_;
goto v___jp_2003_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1978_);
v_a_2027_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2025_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1978_);
v_a_2035_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2021_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2021_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
v___jp_2003_:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Meta_isProp(v___x_2002_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; uint8_t v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2011_ == 0)
{
v___y_1997_ = v_candidates_2004_;
v___y_1998_ = v___x_1999_;
goto v___jp_1996_;
}
else
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_LocalDecl_hasValue(v_val_1990_, v___x_1999_);
if (v___x_2012_ == 0)
{
v___y_1992_ = v_candidates_2004_;
goto v___jp_1991_;
}
else
{
v___y_1997_ = v_candidates_2004_;
v___y_1998_ = v___x_1999_;
goto v___jp_1996_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_candidates_2004_);
lean_del_object(v___x_1978_);
v_a_2013_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2009_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2009_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
v_a_1982_ = v_snd_1976_;
goto v___jp_1981_;
}
v___jp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = l_Lean_LocalDecl_fvarId(v_val_1990_);
v___x_1994_ = lean_box(0);
v___x_1995_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1992_, v___x_1993_, v___x_1994_);
v_a_1982_ = v___x_1995_;
goto v___jp_1981_;
}
v___jp_1996_:
{
if (v___y_1998_ == 0)
{
v_a_1982_ = v___y_1997_;
goto v___jp_1981_;
}
else
{
v___y_1992_ = v___y_1997_;
goto v___jp_1991_;
}
}
}
v___jp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v_a_1982_);
lean_ctor_set(v___x_1978_, 0, v___x_1980_);
v___x_1984_ = v___x_1978_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_a_1982_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
size_t v___x_1985_; size_t v___x_1986_; 
v___x_1985_ = ((size_t)1ULL);
v___x_1986_ = lean_usize_add(v_i_1967_, v___x_1985_);
v_i_1967_ = v___x_1986_;
v_b_1968_ = v___x_1984_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1965_ = stack[0].m_obj;
size_t v_sz_1966_ = stack[1].m_num;
size_t v_i_1967_ = stack[2].m_num;
lean_object* v_b_1968_ = stack[3].m_obj;
lean_object* v___y_1969_ = stack[4].m_obj;
lean_object* v___y_1970_ = stack[5].m_obj;
lean_object* v___y_1971_ = stack[6].m_obj;
lean_object* v___y_1972_ = stack[7].m_obj;
lean_object* v_res_2045_;
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1965_, v_sz_1966_, v_i_1967_, v_b_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_2046_, lean_object* v_sz_2047_, lean_object* v_i_2048_, lean_object* v_b_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
size_t v_sz_boxed_2055_; size_t v_i_boxed_2056_; lean_object* v_res_2057_; 
v_sz_boxed_2055_ = lean_unbox_usize(v_sz_2047_);
lean_dec(v_sz_2047_);
v_i_boxed_2056_ = lean_unbox_usize(v_i_2048_);
lean_dec(v_i_2048_);
v_res_2057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_2046_, v_sz_boxed_2055_, v_i_boxed_2056_, v_b_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec_ref(v_as_2046_);
return v_res_2057_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_b_2061_);
return v___x_2068_;
}
else
{
lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2136_; 
v_snd_2069_ = lean_ctor_get(v_b_2061_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_b_2061_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_b_2061_, 0);
lean_dec(v_unused_2137_);
v___x_2071_ = v_b_2061_;
v_isShared_2072_ = v_isSharedCheck_2136_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_dec(v_b_2061_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2136_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v_a_2075_; lean_object* v_a_2082_; 
v___x_2073_ = lean_box(0);
v_a_2082_ = lean_array_uget_borrowed(v_as_2058_, v_i_2060_);
if (lean_obj_tag(v_a_2082_) == 0)
{
v_a_2075_ = v_snd_2069_;
goto v___jp_2074_;
}
else
{
lean_object* v_val_2083_; lean_object* v___y_2085_; lean_object* v___y_2090_; uint8_t v___y_2091_; uint8_t v___x_2092_; 
v_val_2083_ = lean_ctor_get(v_a_2082_, 0);
v___x_2092_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2083_);
if (v___x_2092_ == 0)
{
lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; lean_object* v_candidates_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2114_; 
v___f_2093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2095_ = l_Lean_LocalDecl_type(v_val_2083_);
lean_inc_ref(v___x_2095_);
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2093_, v___f_2094_, v___x_2092_, v___x_2095_, v_snd_2069_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_LocalDecl_value_x3f(v_val_2083_, v___x_2092_);
if (lean_obj_tag(v___x_2116_) == 0)
{
v_candidates_2097_ = v_a_2115_;
v___y_2098_ = v___y_2062_;
v___y_2099_ = v___y_2063_;
v___y_2100_ = v___y_2064_;
v___y_2101_ = v___y_2065_;
goto v___jp_2096_;
}
else
{
lean_object* v_val_2117_; lean_object* v___x_2118_; 
v_val_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2093_, v___f_2094_, v___x_2092_, v_val_2117_, v_a_2115_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v_candidates_2097_ = v_a_2119_;
v___y_2098_ = v___y_2062_;
v___y_2099_ = v___y_2063_;
v___y_2100_ = v___y_2064_;
v___y_2101_ = v___y_2065_;
goto v___jp_2096_;
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v___x_2095_);
lean_del_object(v___x_2071_);
v_a_2120_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2118_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2118_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___x_2095_);
lean_del_object(v___x_2071_);
v_a_2128_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2114_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2114_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
v___jp_2096_:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Meta_isProp(v___x_2095_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = lean_unbox(v_a_2103_);
lean_dec(v_a_2103_);
if (v___x_2104_ == 0)
{
v___y_2090_ = v_candidates_2097_;
v___y_2091_ = v___x_2092_;
goto v___jp_2089_;
}
else
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_LocalDecl_hasValue(v_val_2083_, v___x_2092_);
if (v___x_2105_ == 0)
{
v___y_2085_ = v_candidates_2097_;
goto v___jp_2084_;
}
else
{
v___y_2090_ = v_candidates_2097_;
v___y_2091_ = v___x_2092_;
goto v___jp_2089_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v_candidates_2097_);
lean_del_object(v___x_2071_);
v_a_2106_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2102_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2102_);
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
}
else
{
v_a_2075_ = v_snd_2069_;
goto v___jp_2074_;
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_LocalDecl_fvarId(v_val_2083_);
v___x_2087_ = lean_box(0);
v___x_2088_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2085_, v___x_2086_, v___x_2087_);
v_a_2075_ = v___x_2088_;
goto v___jp_2074_;
}
v___jp_2089_:
{
if (v___y_2091_ == 0)
{
v_a_2075_ = v___y_2090_;
goto v___jp_2074_;
}
else
{
v___y_2085_ = v___y_2090_;
goto v___jp_2084_;
}
}
}
v___jp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v_a_2075_);
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2077_ = v___x_2071_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_a_2075_);
v___x_2077_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2060_, v___x_2078_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_2058_, v_sz_2059_, v___x_2079_, v___x_2077_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2058_ = stack[0].m_obj;
size_t v_sz_2059_ = stack[1].m_num;
size_t v_i_2060_ = stack[2].m_num;
lean_object* v_b_2061_ = stack[3].m_obj;
lean_object* v___y_2062_ = stack[4].m_obj;
lean_object* v___y_2063_ = stack[5].m_obj;
lean_object* v___y_2064_ = stack[6].m_obj;
lean_object* v___y_2065_ = stack[7].m_obj;
lean_object* v_res_2138_;
v_res_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2058_, v_sz_2059_, v_i_2060_, v_b_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
stack->m_obj
 = v_res_2138_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2139_, lean_object* v_sz_2140_, lean_object* v_i_2141_, lean_object* v_b_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
size_t v_sz_boxed_2148_; size_t v_i_boxed_2149_; lean_object* v_res_2150_; 
v_sz_boxed_2148_ = lean_unbox_usize(v_sz_2140_);
lean_dec(v_sz_2140_);
v_i_boxed_2149_ = lean_unbox_usize(v_i_2141_);
lean_dec(v_i_2141_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2139_, v_sz_boxed_2148_, v_i_boxed_2149_, v_b_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v_as_2139_);
return v_res_2150_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2151_, lean_object* v_n_2152_, lean_object* v_b_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
if (lean_obj_tag(v_n_2152_) == 0)
{
lean_object* v_cs_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; size_t v_sz_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v_cs_2159_ = lean_ctor_get(v_n_2152_, 0);
v___x_2160_ = lean_box(0);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_b_2153_);
v_sz_2162_ = lean_array_size(v_cs_2159_);
v___x_2163_ = ((size_t)0ULL);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2151_, v_cs_2159_, v_sz_2162_, v___x_2163_, v___x_2161_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2179_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2179_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2179_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_fst_2169_; 
v_fst_2169_ = lean_ctor_get(v_a_2165_, 0);
if (lean_obj_tag(v_fst_2169_) == 0)
{
lean_object* v_snd_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v_snd_2170_ = lean_ctor_get(v_a_2165_, 1);
lean_inc(v_snd_2170_);
lean_dec(v_a_2165_);
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_snd_2170_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2171_);
v___x_2173_ = v___x_2167_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
else
{
lean_object* v_val_2175_; lean_object* v___x_2177_; 
lean_inc_ref(v_fst_2169_);
lean_dec(v_a_2165_);
v_val_2175_ = lean_ctor_get(v_fst_2169_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v_fst_2169_, 1);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_val_2175_);
v___x_2177_ = v___x_2167_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_val_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2164_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2164_);
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
else
{
lean_object* v_vs_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; size_t v_sz_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
v_vs_2188_ = lean_ctor_get(v_n_2152_, 0);
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_b_2153_);
v_sz_2191_ = lean_array_size(v_vs_2188_);
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2188_, v_sz_2191_, v___x_2192_, v___x_2190_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2208_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_fst_2198_; 
v_fst_2198_ = lean_ctor_get(v_a_2194_, 0);
if (lean_obj_tag(v_fst_2198_) == 0)
{
lean_object* v_snd_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v_snd_2199_ = lean_ctor_get(v_a_2194_, 1);
lean_inc(v_snd_2199_);
lean_dec(v_a_2194_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_snd_2199_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2200_);
v___x_2202_ = v___x_2196_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
else
{
lean_object* v_val_2204_; lean_object* v___x_2206_; 
lean_inc_ref(v_fst_2198_);
lean_dec(v_a_2194_);
v_val_2204_ = lean_ctor_get(v_fst_2198_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v_fst_2198_, 1);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v_val_2204_);
v___x_2206_ = v___x_2196_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_val_2204_);
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
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2193_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2193_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2151_ = stack[0].m_obj;
lean_object* v_n_2152_ = stack[1].m_obj;
lean_object* v_b_2153_ = stack[2].m_obj;
lean_object* v___y_2154_ = stack[3].m_obj;
lean_object* v___y_2155_ = stack[4].m_obj;
lean_object* v___y_2156_ = stack[5].m_obj;
lean_object* v___y_2157_ = stack[6].m_obj;
lean_object* v_res_2217_;
v_res_2217_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2151_, v_n_2152_, v_b_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
stack->m_obj
 = v_res_2217_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2218_, lean_object* v_as_2219_, size_t v_sz_2220_, size_t v_i_2221_, lean_object* v_b_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_usize_dec_lt(v_i_2221_, v_sz_2220_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_b_2222_);
return v___x_2229_;
}
else
{
lean_object* v_snd_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2264_; 
v_snd_2230_ = lean_ctor_get(v_b_2222_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_b_2222_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v_b_2222_, 0);
lean_dec(v_unused_2265_);
v___x_2232_ = v_b_2222_;
v_isShared_2233_ = v_isSharedCheck_2264_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_snd_2230_);
lean_dec(v_b_2222_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2264_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v_a_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_box(0);
v_a_2235_ = lean_array_uget_borrowed(v_as_2219_, v_i_2221_);
lean_inc(v_snd_2230_);
v___x_2236_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2218_, v_a_2235_, v_snd_2230_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2255_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2255_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2255_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
if (lean_obj_tag(v_a_2237_) == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2237_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2241_);
v___x_2243_ = v___x_2232_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_snd_2230_);
v___x_2243_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2243_);
v___x_2245_ = v___x_2239_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; 
lean_del_object(v___x_2239_);
lean_dec(v_snd_2230_);
v_a_2248_ = lean_ctor_get(v_a_2237_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v_a_2237_, 1);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_a_2248_);
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2250_ = v___x_2232_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_a_2248_);
v___x_2250_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
size_t v___x_2251_; size_t v___x_2252_; 
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_add(v_i_2221_, v___x_2251_);
v_i_2221_ = v___x_2252_;
v_b_2222_ = v___x_2250_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_del_object(v___x_2232_);
lean_dec(v_snd_2230_);
v_a_2256_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2236_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2236_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2218_ = stack[0].m_obj;
lean_object* v_as_2219_ = stack[1].m_obj;
size_t v_sz_2220_ = stack[2].m_num;
size_t v_i_2221_ = stack[3].m_num;
lean_object* v_b_2222_ = stack[4].m_obj;
lean_object* v___y_2223_ = stack[5].m_obj;
lean_object* v___y_2224_ = stack[6].m_obj;
lean_object* v___y_2225_ = stack[7].m_obj;
lean_object* v___y_2226_ = stack[8].m_obj;
lean_object* v_res_2266_;
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2218_, v_as_2219_, v_sz_2220_, v_i_2221_, v_b_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
stack->m_obj
 = v_res_2266_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2267_, lean_object* v_as_2268_, lean_object* v_sz_2269_, lean_object* v_i_2270_, lean_object* v_b_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
size_t v_sz_boxed_2277_; size_t v_i_boxed_2278_; lean_object* v_res_2279_; 
v_sz_boxed_2277_ = lean_unbox_usize(v_sz_2269_);
lean_dec(v_sz_2269_);
v_i_boxed_2278_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2267_, v_as_2268_, v_sz_boxed_2277_, v_i_boxed_2278_, v_b_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_as_2268_);
lean_dec_ref(v_init_2267_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2280_, lean_object* v_n_2281_, lean_object* v_b_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2280_, v_n_2281_, v_b_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec_ref(v_n_2281_);
lean_dec_ref(v_init_2280_);
return v_res_2288_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2289_, lean_object* v_init_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_root_2296_; lean_object* v_tail_2297_; lean_object* v___x_2298_; 
v_root_2296_ = lean_ctor_get(v_t_2289_, 0);
v_tail_2297_ = lean_ctor_get(v_t_2289_, 1);
lean_inc_ref(v_init_2290_);
v___x_2298_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2290_, v_root_2296_, v_init_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec_ref(v_init_2290_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2335_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2335_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2335_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
if (lean_obj_tag(v_a_2299_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; 
v_a_2303_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v_a_2299_, 1);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_a_2303_);
v___x_2305_ = v___x_2301_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; size_t v_sz_2310_; size_t v___x_2311_; lean_object* v___x_2312_; 
lean_del_object(v___x_2301_);
v_a_2307_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v_a_2299_, 1);
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v_a_2307_);
v_sz_2310_ = lean_array_size(v_tail_2297_);
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2297_, v_sz_2310_, v___x_2311_, v___x_2309_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2326_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2326_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2326_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_fst_2317_; 
v_fst_2317_ = lean_ctor_get(v_a_2313_, 0);
if (lean_obj_tag(v_fst_2317_) == 0)
{
lean_object* v_snd_2318_; lean_object* v___x_2320_; 
v_snd_2318_ = lean_ctor_get(v_a_2313_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_snd_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_snd_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
else
{
lean_object* v_val_2322_; lean_object* v___x_2324_; 
lean_inc_ref(v_fst_2317_);
lean_dec(v_a_2313_);
v_val_2322_ = lean_ctor_get(v_fst_2317_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v_fst_2317_, 1);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_val_2322_);
v___x_2324_ = v___x_2315_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_val_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_a_2327_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2312_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2312_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v_a_2336_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2298_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2298_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2289_ = stack[0].m_obj;
lean_object* v_init_2290_ = stack[1].m_obj;
lean_object* v___y_2291_ = stack[2].m_obj;
lean_object* v___y_2292_ = stack[3].m_obj;
lean_object* v___y_2293_ = stack[4].m_obj;
lean_object* v___y_2294_ = stack[5].m_obj;
lean_object* v_res_2344_;
v_res_2344_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2289_, v_init_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
stack->m_obj
 = v_res_2344_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2345_, lean_object* v_init_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2345_, v_init_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_t_2345_);
return v_res_2352_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_buckets_2355_; lean_object* v___x_2356_; uint64_t v___x_2357_; uint64_t v___x_2358_; uint64_t v___x_2359_; uint64_t v_fold_2360_; uint64_t v___x_2361_; uint64_t v___x_2362_; uint64_t v___x_2363_; size_t v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; size_t v___x_2367_; size_t v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_buckets_2355_ = lean_ctor_get(v_m_2353_, 1);
v___x_2356_ = lean_array_get_size(v_buckets_2355_);
v___x_2357_ = l_Lean_instHashableFVarId_hash(v_a_2354_);
v___x_2358_ = 32ULL;
v___x_2359_ = lean_uint64_shift_right(v___x_2357_, v___x_2358_);
v_fold_2360_ = lean_uint64_xor(v___x_2357_, v___x_2359_);
v___x_2361_ = 16ULL;
v___x_2362_ = lean_uint64_shift_right(v_fold_2360_, v___x_2361_);
v___x_2363_ = lean_uint64_xor(v_fold_2360_, v___x_2362_);
v___x_2364_ = lean_uint64_to_usize(v___x_2363_);
v___x_2365_ = lean_usize_of_nat(v___x_2356_);
v___x_2366_ = ((size_t)1ULL);
v___x_2367_ = lean_usize_sub(v___x_2365_, v___x_2366_);
v___x_2368_ = lean_usize_land(v___x_2364_, v___x_2367_);
v___x_2369_ = lean_array_uget_borrowed(v_buckets_2355_, v___x_2368_);
v___x_2370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2354_, v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2353_ = stack[0].m_obj;
lean_object* v_a_2354_ = stack[1].m_obj;
uint8_t v_res_2371_;
v_res_2371_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2353_, v_a_2354_);
stack->m_num = v_res_2371_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2372_, lean_object* v_a_2373_){
_start:
{
uint8_t v_res_2374_; lean_object* v_r_2375_; 
v_res_2374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_m_2372_);
v_r_2375_ = lean_box(v_res_2374_);
return v_r_2375_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2376_, lean_object* v_as_2377_, size_t v_sz_2378_, size_t v_i_2379_, lean_object* v_b_2380_){
_start:
{
uint8_t v___x_2382_; 
v___x_2382_ = lean_usize_dec_lt(v_i_2379_, v_sz_2378_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_b_2380_);
return v___x_2383_;
}
else
{
lean_object* v_snd_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2402_; 
v_snd_2384_ = lean_ctor_get(v_b_2380_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_b_2380_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; 
v_unused_2403_ = lean_ctor_get(v_b_2380_, 0);
lean_dec(v_unused_2403_);
v___x_2386_ = v_b_2380_;
v_isShared_2387_ = v_isSharedCheck_2402_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_snd_2384_);
lean_dec(v_b_2380_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2402_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v_a_2390_; lean_object* v_a_2397_; 
v___x_2388_ = lean_box(0);
v_a_2397_ = lean_array_uget_borrowed(v_as_2377_, v_i_2379_);
if (lean_obj_tag(v_a_2397_) == 0)
{
v_a_2390_ = v_snd_2384_;
goto v___jp_2389_;
}
else
{
lean_object* v_val_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v_val_2398_ = lean_ctor_get(v_a_2397_, 0);
v___x_2399_ = l_Lean_LocalDecl_fvarId(v_val_2398_);
v___x_2400_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2376_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_dec(v___x_2399_);
v_a_2390_ = v_snd_2384_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_array_push(v_snd_2384_, v___x_2399_);
v_a_2390_ = v___x_2401_;
goto v___jp_2389_;
}
}
v___jp_2389_:
{
lean_object* v___x_2392_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v_a_2390_);
lean_ctor_set(v___x_2386_, 0, v___x_2388_);
v___x_2392_ = v___x_2386_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_a_2390_);
v___x_2392_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
size_t v___x_2393_; size_t v___x_2394_; 
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_i_2379_, v___x_2393_);
v_i_2379_ = v___x_2394_;
v_b_2380_ = v___x_2392_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2376_ = stack[0].m_obj;
lean_object* v_as_2377_ = stack[1].m_obj;
size_t v_sz_2378_ = stack[2].m_num;
size_t v_i_2379_ = stack[3].m_num;
lean_object* v_b_2380_ = stack[4].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2376_, v_as_2377_, v_sz_2378_, v_i_2379_, v_b_2380_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2405_, lean_object* v_as_2406_, lean_object* v_sz_2407_, lean_object* v_i_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_){
_start:
{
size_t v_sz_boxed_2411_; size_t v_i_boxed_2412_; lean_object* v_res_2413_; 
v_sz_boxed_2411_ = lean_unbox_usize(v_sz_2407_);
lean_dec(v_sz_2407_);
v_i_boxed_2412_ = lean_unbox_usize(v_i_2408_);
lean_dec(v_i_2408_);
v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2405_, v_as_2406_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2409_);
lean_dec_ref(v_as_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2413_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2414_, lean_object* v_as_2415_, size_t v_sz_2416_, size_t v_i_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_lt(v_i_2417_, v_sz_2416_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_b_2418_);
return v___x_2425_;
}
else
{
lean_object* v_snd_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2444_; 
v_snd_2426_ = lean_ctor_get(v_b_2418_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_b_2418_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v_b_2418_, 0);
lean_dec(v_unused_2445_);
v___x_2428_ = v_b_2418_;
v_isShared_2429_ = v_isSharedCheck_2444_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_snd_2426_);
lean_dec(v_b_2418_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2444_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v_a_2432_; lean_object* v_a_2439_; 
v___x_2430_ = lean_box(0);
v_a_2439_ = lean_array_uget_borrowed(v_as_2415_, v_i_2417_);
if (lean_obj_tag(v_a_2439_) == 0)
{
v_a_2432_ = v_snd_2426_;
goto v___jp_2431_;
}
else
{
lean_object* v_val_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v_val_2440_ = lean_ctor_get(v_a_2439_, 0);
v___x_2441_ = l_Lean_LocalDecl_fvarId(v_val_2440_);
v___x_2442_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2414_, v___x_2441_);
if (v___x_2442_ == 0)
{
lean_dec(v___x_2441_);
v_a_2432_ = v_snd_2426_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_array_push(v_snd_2426_, v___x_2441_);
v_a_2432_ = v___x_2443_;
goto v___jp_2431_;
}
}
v___jp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 1, v_a_2432_);
lean_ctor_set(v___x_2428_, 0, v___x_2430_);
v___x_2434_ = v___x_2428_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_a_2432_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = ((size_t)1ULL);
v___x_2436_ = lean_usize_add(v_i_2417_, v___x_2435_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2414_, v_as_2415_, v_sz_2416_, v___x_2436_, v___x_2434_);
return v___x_2437_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2414_ = stack[0].m_obj;
lean_object* v_as_2415_ = stack[1].m_obj;
size_t v_sz_2416_ = stack[2].m_num;
size_t v_i_2417_ = stack[3].m_num;
lean_object* v_b_2418_ = stack[4].m_obj;
lean_object* v___y_2419_ = stack[5].m_obj;
lean_object* v___y_2420_ = stack[6].m_obj;
lean_object* v___y_2421_ = stack[7].m_obj;
lean_object* v___y_2422_ = stack[8].m_obj;
lean_object* v_res_2446_;
v_res_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2414_, v_as_2415_, v_sz_2416_, v_i_2417_, v_b_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
stack->m_obj
 = v_res_2446_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2447_, lean_object* v_as_2448_, lean_object* v_sz_2449_, lean_object* v_i_2450_, lean_object* v_b_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
size_t v_sz_boxed_2457_; size_t v_i_boxed_2458_; lean_object* v_res_2459_; 
v_sz_boxed_2457_ = lean_unbox_usize(v_sz_2449_);
lean_dec(v_sz_2449_);
v_i_boxed_2458_ = lean_unbox_usize(v_i_2450_);
lean_dec(v_i_2450_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2447_, v_as_2448_, v_sz_boxed_2457_, v_i_boxed_2458_, v_b_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec_ref(v_as_2448_);
lean_dec_ref(v_a_2447_);
return v_res_2459_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2460_, lean_object* v_a_2461_, lean_object* v_n_2462_, lean_object* v_b_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
if (lean_obj_tag(v_n_2462_) == 0)
{
lean_object* v_cs_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; size_t v_sz_2472_; size_t v___x_2473_; lean_object* v___x_2474_; 
v_cs_2469_ = lean_ctor_get(v_n_2462_, 0);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v_b_2463_);
v_sz_2472_ = lean_array_size(v_cs_2469_);
v___x_2473_ = ((size_t)0ULL);
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2460_, v_a_2461_, v_cs_2469_, v_sz_2472_, v___x_2473_, v___x_2471_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2489_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2489_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2489_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_fst_2479_; 
v_fst_2479_ = lean_ctor_get(v_a_2475_, 0);
if (lean_obj_tag(v_fst_2479_) == 0)
{
lean_object* v_snd_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v_snd_2480_ = lean_ctor_get(v_a_2475_, 1);
lean_inc(v_snd_2480_);
lean_dec(v_a_2475_);
v___x_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_snd_2480_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2481_);
v___x_2483_ = v___x_2477_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
else
{
lean_object* v_val_2485_; lean_object* v___x_2487_; 
lean_inc_ref(v_fst_2479_);
lean_dec(v_a_2475_);
v_val_2485_ = lean_ctor_get(v_fst_2479_, 0);
lean_inc(v_val_2485_);
lean_dec_ref_known(v_fst_2479_, 1);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v_val_2485_);
v___x_2487_ = v___x_2477_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_val_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2474_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2474_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_object* v_vs_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; size_t v_sz_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v_vs_2498_ = lean_ctor_get(v_n_2462_, 0);
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v_b_2463_);
v_sz_2501_ = lean_array_size(v_vs_2498_);
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2461_, v_vs_2498_, v_sz_2501_, v___x_2502_, v___x_2500_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2518_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2518_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2518_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v_fst_2508_; 
v_fst_2508_ = lean_ctor_get(v_a_2504_, 0);
if (lean_obj_tag(v_fst_2508_) == 0)
{
lean_object* v_snd_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v_snd_2509_ = lean_ctor_get(v_a_2504_, 1);
lean_inc(v_snd_2509_);
lean_dec(v_a_2504_);
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_snd_2509_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2510_);
v___x_2512_ = v___x_2506_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
else
{
lean_object* v_val_2514_; lean_object* v___x_2516_; 
lean_inc_ref(v_fst_2508_);
lean_dec(v_a_2504_);
v_val_2514_ = lean_ctor_get(v_fst_2508_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v_fst_2508_, 1);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v_val_2514_);
v___x_2516_ = v___x_2506_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_val_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_a_2519_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2503_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2503_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2460_ = stack[0].m_obj;
lean_object* v_a_2461_ = stack[1].m_obj;
lean_object* v_n_2462_ = stack[2].m_obj;
lean_object* v_b_2463_ = stack[3].m_obj;
lean_object* v___y_2464_ = stack[4].m_obj;
lean_object* v___y_2465_ = stack[5].m_obj;
lean_object* v___y_2466_ = stack[6].m_obj;
lean_object* v___y_2467_ = stack[7].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2460_, v_a_2461_, v_n_2462_, v_b_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
stack->m_obj
 = v_res_2527_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2528_, lean_object* v_a_2529_, lean_object* v_as_2530_, size_t v_sz_2531_, size_t v_i_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_lt(v_i_2532_, v_sz_2531_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_b_2533_);
return v___x_2540_;
}
else
{
lean_object* v_snd_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2575_; 
v_snd_2541_ = lean_ctor_get(v_b_2533_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_b_2533_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_b_2533_, 0);
lean_dec(v_unused_2576_);
v___x_2543_ = v_b_2533_;
v_isShared_2544_ = v_isSharedCheck_2575_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snd_2541_);
lean_dec(v_b_2533_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2575_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v_a_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(0);
v_a_2546_ = lean_array_uget_borrowed(v_as_2530_, v_i_2532_);
lean_inc(v_snd_2541_);
v___x_2547_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2528_, v_a_2529_, v_a_2546_, v_snd_2541_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2566_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2566_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2566_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
if (lean_obj_tag(v_a_2548_) == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_a_2548_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2552_);
v___x_2554_ = v___x_2543_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_snd_2541_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2556_; 
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2554_);
v___x_2556_ = v___x_2550_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; 
lean_del_object(v___x_2550_);
lean_dec(v_snd_2541_);
v_a_2559_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v_a_2548_, 1);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 1, v_a_2559_);
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2561_ = v___x_2543_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_a_2559_);
v___x_2561_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
size_t v___x_2562_; size_t v___x_2563_; 
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_add(v_i_2532_, v___x_2562_);
v_i_2532_ = v___x_2563_;
v_b_2533_ = v___x_2561_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_del_object(v___x_2543_);
lean_dec(v_snd_2541_);
v_a_2567_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2547_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2547_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2528_ = stack[0].m_obj;
lean_object* v_a_2529_ = stack[1].m_obj;
lean_object* v_as_2530_ = stack[2].m_obj;
size_t v_sz_2531_ = stack[3].m_num;
size_t v_i_2532_ = stack[4].m_num;
lean_object* v_b_2533_ = stack[5].m_obj;
lean_object* v___y_2534_ = stack[6].m_obj;
lean_object* v___y_2535_ = stack[7].m_obj;
lean_object* v___y_2536_ = stack[8].m_obj;
lean_object* v___y_2537_ = stack[9].m_obj;
lean_object* v_res_2577_;
v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2528_, v_a_2529_, v_as_2530_, v_sz_2531_, v_i_2532_, v_b_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
stack->m_obj
 = v_res_2577_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2578_, lean_object* v_a_2579_, lean_object* v_as_2580_, lean_object* v_sz_2581_, lean_object* v_i_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
size_t v_sz_boxed_2589_; size_t v_i_boxed_2590_; lean_object* v_res_2591_; 
v_sz_boxed_2589_ = lean_unbox_usize(v_sz_2581_);
lean_dec(v_sz_2581_);
v_i_boxed_2590_ = lean_unbox_usize(v_i_2582_);
lean_dec(v_i_2582_);
v_res_2591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2578_, v_a_2579_, v_as_2580_, v_sz_boxed_2589_, v_i_boxed_2590_, v_b_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_as_2580_);
lean_dec_ref(v_a_2579_);
lean_dec_ref(v_init_2578_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2592_, lean_object* v_a_2593_, lean_object* v_n_2594_, lean_object* v_b_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2592_, v_a_2593_, v_n_2594_, v_b_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v_n_2594_);
lean_dec_ref(v_a_2593_);
lean_dec_ref(v_init_2592_);
return v_res_2601_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2602_, lean_object* v_as_2603_, size_t v_sz_2604_, size_t v_i_2605_, lean_object* v_b_2606_){
_start:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_usize_dec_lt(v_i_2605_, v_sz_2604_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_b_2606_);
return v___x_2609_;
}
else
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2628_; 
v_snd_2610_ = lean_ctor_get(v_b_2606_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_b_2606_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v_b_2606_, 0);
lean_dec(v_unused_2629_);
v___x_2612_ = v_b_2606_;
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_dec(v_b_2606_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v_a_2616_; lean_object* v_a_2623_; 
v___x_2614_ = lean_box(0);
v_a_2623_ = lean_array_uget_borrowed(v_as_2603_, v_i_2605_);
if (lean_obj_tag(v_a_2623_) == 0)
{
v_a_2616_ = v_snd_2610_;
goto v___jp_2615_;
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v_val_2624_ = lean_ctor_get(v_a_2623_, 0);
v___x_2625_ = l_Lean_LocalDecl_fvarId(v_val_2624_);
v___x_2626_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2602_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_dec(v___x_2625_);
v_a_2616_ = v_snd_2610_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_array_push(v_snd_2610_, v___x_2625_);
v_a_2616_ = v___x_2627_;
goto v___jp_2615_;
}
}
v___jp_2615_:
{
lean_object* v___x_2618_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 1, v_a_2616_);
lean_ctor_set(v___x_2612_, 0, v___x_2614_);
v___x_2618_ = v___x_2612_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_a_2616_);
v___x_2618_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
size_t v___x_2619_; size_t v___x_2620_; 
v___x_2619_ = ((size_t)1ULL);
v___x_2620_ = lean_usize_add(v_i_2605_, v___x_2619_);
v_i_2605_ = v___x_2620_;
v_b_2606_ = v___x_2618_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2602_ = stack[0].m_obj;
lean_object* v_as_2603_ = stack[1].m_obj;
size_t v_sz_2604_ = stack[2].m_num;
size_t v_i_2605_ = stack[3].m_num;
lean_object* v_b_2606_ = stack[4].m_obj;
lean_object* v_res_2630_;
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2602_, v_as_2603_, v_sz_2604_, v_i_2605_, v_b_2606_);
stack->m_obj
 = v_res_2630_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2631_, lean_object* v_as_2632_, lean_object* v_sz_2633_, lean_object* v_i_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2631_, v_as_2632_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2635_);
lean_dec_ref(v_as_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2639_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2640_, lean_object* v_as_2641_, size_t v_sz_2642_, size_t v_i_2643_, lean_object* v_b_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_usize_dec_lt(v_i_2643_, v_sz_2642_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_b_2644_);
return v___x_2651_;
}
else
{
lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2670_; 
v_snd_2652_ = lean_ctor_get(v_b_2644_, 1);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_b_2644_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v_b_2644_, 0);
lean_dec(v_unused_2671_);
v___x_2654_ = v_b_2644_;
v_isShared_2655_ = v_isSharedCheck_2670_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_dec(v_b_2644_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2670_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v_a_2658_; lean_object* v_a_2665_; 
v___x_2656_ = lean_box(0);
v_a_2665_ = lean_array_uget_borrowed(v_as_2641_, v_i_2643_);
if (lean_obj_tag(v_a_2665_) == 0)
{
v_a_2658_ = v_snd_2652_;
goto v___jp_2657_;
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_val_2666_ = lean_ctor_get(v_a_2665_, 0);
v___x_2667_ = l_Lean_LocalDecl_fvarId(v_val_2666_);
v___x_2668_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2640_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_dec(v___x_2667_);
v_a_2658_ = v_snd_2652_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_array_push(v_snd_2652_, v___x_2667_);
v_a_2658_ = v___x_2669_;
goto v___jp_2657_;
}
}
v___jp_2657_:
{
lean_object* v___x_2660_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v_a_2658_);
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2660_ = v___x_2654_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_a_2658_);
v___x_2660_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((size_t)1ULL);
v___x_2662_ = lean_usize_add(v_i_2643_, v___x_2661_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2640_, v_as_2641_, v_sz_2642_, v___x_2662_, v___x_2660_);
return v___x_2663_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2640_ = stack[0].m_obj;
lean_object* v_as_2641_ = stack[1].m_obj;
size_t v_sz_2642_ = stack[2].m_num;
size_t v_i_2643_ = stack[3].m_num;
lean_object* v_b_2644_ = stack[4].m_obj;
lean_object* v___y_2645_ = stack[5].m_obj;
lean_object* v___y_2646_ = stack[6].m_obj;
lean_object* v___y_2647_ = stack[7].m_obj;
lean_object* v___y_2648_ = stack[8].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2640_, v_as_2641_, v_sz_2642_, v_i_2643_, v_b_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2673_, lean_object* v_as_2674_, lean_object* v_sz_2675_, lean_object* v_i_2676_, lean_object* v_b_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
size_t v_sz_boxed_2683_; size_t v_i_boxed_2684_; lean_object* v_res_2685_; 
v_sz_boxed_2683_ = lean_unbox_usize(v_sz_2675_);
lean_dec(v_sz_2675_);
v_i_boxed_2684_ = lean_unbox_usize(v_i_2676_);
lean_dec(v_i_2676_);
v_res_2685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2673_, v_as_2674_, v_sz_boxed_2683_, v_i_boxed_2684_, v_b_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_as_2674_);
lean_dec_ref(v_a_2673_);
return v_res_2685_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2686_, lean_object* v_t_2687_, lean_object* v_init_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_root_2694_; lean_object* v_tail_2695_; lean_object* v___x_2696_; 
v_root_2694_ = lean_ctor_get(v_t_2687_, 0);
v_tail_2695_ = lean_ctor_get(v_t_2687_, 1);
lean_inc_ref(v_init_2688_);
v___x_2696_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2688_, v_a_2686_, v_root_2694_, v_init_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec_ref(v_init_2688_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2733_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2733_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2733_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
if (lean_obj_tag(v_a_2697_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; 
v_a_2701_ = lean_ctor_get(v_a_2697_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v_a_2697_, 1);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_a_2701_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; size_t v_sz_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
lean_del_object(v___x_2699_);
v_a_2705_ = lean_ctor_get(v_a_2697_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v_a_2697_, 1);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v_a_2705_);
v_sz_2708_ = lean_array_size(v_tail_2695_);
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2686_, v_tail_2695_, v_sz_2708_, v___x_2709_, v___x_2707_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2724_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2724_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2724_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_fst_2715_; 
v_fst_2715_ = lean_ctor_get(v_a_2711_, 0);
if (lean_obj_tag(v_fst_2715_) == 0)
{
lean_object* v_snd_2716_; lean_object* v___x_2718_; 
v_snd_2716_ = lean_ctor_get(v_a_2711_, 1);
lean_inc(v_snd_2716_);
lean_dec(v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_snd_2716_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_snd_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2722_; 
lean_inc_ref(v_fst_2715_);
lean_dec(v_a_2711_);
v_val_2720_ = lean_ctor_get(v_fst_2715_, 0);
lean_inc(v_val_2720_);
lean_dec_ref_known(v_fst_2715_, 1);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_val_2720_);
v___x_2722_ = v___x_2713_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_val_2720_);
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
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2710_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2710_);
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
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
v_a_2734_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2696_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2696_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2686_ = stack[0].m_obj;
lean_object* v_t_2687_ = stack[1].m_obj;
lean_object* v_init_2688_ = stack[2].m_obj;
lean_object* v___y_2689_ = stack[3].m_obj;
lean_object* v___y_2690_ = stack[4].m_obj;
lean_object* v___y_2691_ = stack[5].m_obj;
lean_object* v___y_2692_ = stack[6].m_obj;
lean_object* v_res_2742_;
v_res_2742_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2686_, v_t_2687_, v_init_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
stack->m_obj
 = v_res_2742_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2743_, lean_object* v_t_2744_, lean_object* v_init_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2743_, v_t_2744_, v_init_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec_ref(v_t_2744_);
lean_dec_ref(v_a_2743_);
return v_res_2751_;
}
}
lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2754_, lean_object* v_mvarId_2755_, lean_object* v___f_2756_, lean_object* v___f_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_lctx_2763_; lean_object* v_decls_2764_; lean_object* v___x_2765_; 
v_lctx_2763_ = lean_ctor_get(v___y_2758_, 2);
v_decls_2764_ = lean_ctor_get(v_lctx_2763_, 1);
lean_inc_ref(v_decls_2764_);
v___x_2765_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2764_, v_candidates_2754_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = l_Lean_MVarId_getType(v_mvarId_2755_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; lean_object* v_a_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___y_2774_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2768_, v___y_2759_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref(v___x_2769_);
v___x_2771_ = l_Lean_Expr_hasFVar(v_a_2770_);
v___x_2772_ = lean_st_mk_ref(v_a_2766_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v_a_2770_);
lean_dec_ref(v___f_2757_);
v___x_2798_ = lean_box(0);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___x_2772_);
v___x_2799_ = lean_apply_7(v___f_2756_, v___x_2798_, v___x_2772_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, lean_box(0));
v___y_2774_ = v___x_2799_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2801_ = 0;
v___x_2802_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2800_, v___f_2757_, v_a_2770_, v___x_2801_, v___x_2772_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v___x_2772_);
v___x_2804_ = lean_apply_7(v___f_2756_, v_a_2803_, v___x_2772_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, lean_box(0));
v___y_2774_ = v___x_2804_;
goto v___jp_2773_;
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v___x_2772_);
lean_dec_ref(v_decls_2764_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v___f_2756_);
v_a_2805_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2802_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2802_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
v___jp_2773_:
{
if (lean_obj_tag(v___y_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2789_; 
v_a_2775_ = lean_ctor_get(v___y_2774_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___y_2774_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2777_ = v___y_2774_;
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___y_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2789_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v_size_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2779_ = lean_st_ref_get(v___x_2772_);
lean_dec(v___x_2772_);
lean_dec(v___x_2779_);
v_size_2780_ = lean_ctor_get(v_a_2775_, 0);
v___x_2781_ = lean_unsigned_to_nat(0u);
v___x_2782_ = lean_nat_dec_eq(v_size_2780_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2777_);
v___x_2783_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2784_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2775_, v_decls_2764_, v___x_2783_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v_decls_2764_);
lean_dec(v_a_2775_);
return v___x_2784_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
lean_dec(v_a_2775_);
lean_dec_ref(v_decls_2764_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
v___x_2785_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2785_);
v___x_2787_ = v___x_2777_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v___x_2772_);
lean_dec_ref(v_decls_2764_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
v_a_2790_ = lean_ctor_get(v___y_2774_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___y_2774_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___y_2774_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___y_2774_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_a_2766_);
lean_dec_ref(v_decls_2764_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v___f_2757_);
lean_dec_ref(v___f_2756_);
v_a_2813_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2767_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2767_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref(v_decls_2764_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v___f_2757_);
lean_dec_ref(v___f_2756_);
lean_dec(v_mvarId_2755_);
v_a_2821_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2765_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2765_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_getNondepPropHyps___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_candidates_2754_ = stack[0].m_obj;
lean_object* v_mvarId_2755_ = stack[1].m_obj;
lean_object* v___f_2756_ = stack[2].m_obj;
lean_object* v___f_2757_ = stack[3].m_obj;
lean_object* v___y_2758_ = stack[4].m_obj;
lean_object* v___y_2759_ = stack[5].m_obj;
lean_object* v___y_2760_ = stack[6].m_obj;
lean_object* v___y_2761_ = stack[7].m_obj;
lean_object* v_res_2829_;
v_res_2829_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2754_, v_mvarId_2755_, v___f_2756_, v___f_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
stack->m_obj
 = v_res_2829_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2830_, lean_object* v_mvarId_2831_, lean_object* v___f_2832_, lean_object* v___f_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2830_, v_mvarId_2831_, v___f_2832_, v___f_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
return v_res_2839_;
}
}
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v_candidates_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; 
v___f_2848_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2849_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2850_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2842_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2851_, 0, v_candidates_2850_);
lean_closure_set(v___f_2851_, 1, v_mvarId_2842_);
lean_closure_set(v___f_2851_, 2, v___f_2849_);
lean_closure_set(v___f_2851_, 3, v___f_2848_);
v___x_2852_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2842_, v___f_2851_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
return v___x_2852_;
}
}
LEAN_EXPORT void l_Lean_MVarId_getNondepPropHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2842_ = stack[0].m_obj;
lean_object* v_a_2843_ = stack[1].m_obj;
lean_object* v_a_2844_ = stack[2].m_obj;
lean_object* v_a_2845_ = stack[3].m_obj;
lean_object* v_a_2846_ = stack[4].m_obj;
lean_object* v_res_2853_;
v_res_2853_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
stack->m_obj
 = v_res_2853_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2861_, lean_object* v_m_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2862_, v_a_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2865_, lean_object* v_m_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2865_, v_m_2866_, v_a_2867_);
lean_dec(v_a_2867_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2869_, lean_object* v_m_2870_, lean_object* v_a_2871_, lean_object* v_b_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2870_, v_a_2871_, v_b_2872_);
return v___x_2873_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2874_, lean_object* v_m_2875_, lean_object* v_a_2876_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2875_, v_a_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2875_ = stack[1].m_obj;
lean_object* v_a_2876_ = stack[2].m_obj;
uint8_t v_res_2878_;
v_res_2878_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_box(0), v_m_2875_, v_a_2876_);
stack->m_num = v_res_2878_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2879_, lean_object* v_m_2880_, lean_object* v_a_2881_){
_start:
{
uint8_t v_res_2882_; lean_object* v_r_2883_; 
v_res_2882_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2879_, v_m_2880_, v_a_2881_);
lean_dec(v_a_2881_);
lean_dec_ref(v_m_2880_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2884_, lean_object* v_a_2885_, lean_object* v_x_2886_){
_start:
{
uint8_t v___x_2887_; 
v___x_2887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2885_, v_x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2885_ = stack[1].m_obj;
lean_object* v_x_2886_ = stack[2].m_obj;
uint8_t v_res_2888_;
v_res_2888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_box(0), v_a_2885_, v_x_2886_);
stack->m_num = v_res_2888_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2889_, lean_object* v_a_2890_, lean_object* v_x_2891_){
_start:
{
uint8_t v_res_2892_; lean_object* v_r_2893_; 
v_res_2892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2889_, v_a_2890_, v_x_2891_);
lean_dec(v_x_2891_);
lean_dec(v_a_2890_);
v_r_2893_ = lean_box(v_res_2892_);
return v_r_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2894_, lean_object* v_a_2895_, lean_object* v_x_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2895_, v_x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2898_, lean_object* v_a_2899_, lean_object* v_x_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2898_, v_a_2899_, v_x_2900_);
lean_dec(v_a_2899_);
return v_res_2901_;
}
}
lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2902_, lean_object* v_a_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2902_, v_a_2903_);
return v___x_2910_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2902_ = stack[0].m_obj;
lean_object* v_a_2903_ = stack[1].m_obj;
lean_object* v___y_2904_ = stack[2].m_obj;
lean_object* v___y_2905_ = stack[3].m_obj;
lean_object* v___y_2906_ = stack[4].m_obj;
lean_object* v___y_2907_ = stack[5].m_obj;
lean_object* v___y_2908_ = stack[6].m_obj;
lean_object* v_res_2911_;
v_res_2911_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2902_, v_a_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
stack->m_obj
 = v_res_2911_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2912_, lean_object* v_a_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2912_, v_a_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec(v_a_2913_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2921_, lean_object* v_data_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2922_);
return v___x_2923_;
}
}
lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2924_, lean_object* v_a_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2924_, v_a_2925_);
return v___x_2932_;
}
}
LEAN_EXPORT void l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2924_ = stack[0].m_obj;
lean_object* v_a_2925_ = stack[1].m_obj;
lean_object* v___y_2926_ = stack[2].m_obj;
lean_object* v___y_2927_ = stack[3].m_obj;
lean_object* v___y_2928_ = stack[4].m_obj;
lean_object* v___y_2929_ = stack[5].m_obj;
lean_object* v___y_2930_ = stack[6].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2924_, v_a_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
stack->m_obj
 = v_res_2933_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2934_, lean_object* v_a_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2934_, v_a_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v_a_2935_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2943_, lean_object* v_i_2944_, lean_object* v_source_2945_, lean_object* v_target_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2944_, v_source_2945_, v_target_2946_);
return v___x_2947_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2948_, lean_object* v_as_2949_, size_t v_sz_2950_, size_t v_i_2951_, lean_object* v_b_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2948_, v_as_2949_, v_sz_2950_, v_i_2951_, v_b_2952_);
return v___x_2958_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2948_ = stack[0].m_obj;
lean_object* v_as_2949_ = stack[1].m_obj;
size_t v_sz_2950_ = stack[2].m_num;
size_t v_i_2951_ = stack[3].m_num;
lean_object* v_b_2952_ = stack[4].m_obj;
lean_object* v___y_2953_ = stack[5].m_obj;
lean_object* v___y_2954_ = stack[6].m_obj;
lean_object* v___y_2955_ = stack[7].m_obj;
lean_object* v___y_2956_ = stack[8].m_obj;
lean_object* v_res_2959_;
v_res_2959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2948_, v_as_2949_, v_sz_2950_, v_i_2951_, v_b_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
stack->m_obj
 = v_res_2959_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2960_, lean_object* v_as_2961_, lean_object* v_sz_2962_, lean_object* v_i_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
size_t v_sz_boxed_2970_; size_t v_i_boxed_2971_; lean_object* v_res_2972_; 
v_sz_boxed_2970_ = lean_unbox_usize(v_sz_2962_);
lean_dec(v_sz_2962_);
v_i_boxed_2971_ = lean_unbox_usize(v_i_2963_);
lean_dec(v_i_2963_);
v_res_2972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2960_, v_as_2961_, v_sz_boxed_2970_, v_i_boxed_2971_, v_b_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_as_2961_);
lean_dec_ref(v_a_2960_);
return v_res_2972_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2973_, lean_object* v_m_2974_, lean_object* v_a_2975_){
_start:
{
uint8_t v___x_2976_; 
v___x_2976_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2974_, v_a_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2974_ = stack[1].m_obj;
lean_object* v_a_2975_ = stack[2].m_obj;
uint8_t v_res_2977_;
v_res_2977_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_box(0), v_m_2974_, v_a_2975_);
stack->m_num = v_res_2977_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2978_, lean_object* v_m_2979_, lean_object* v_a_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2978_, v_m_2979_, v_a_2980_);
lean_dec_ref(v_a_2980_);
lean_dec_ref(v_m_2979_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2983_, lean_object* v_m_2984_, lean_object* v_a_2985_, lean_object* v_b_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2984_, v_a_2985_, v_b_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2989_, v_x_2990_);
return v___x_2991_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2992_, lean_object* v_as_2993_, size_t v_sz_2994_, size_t v_i_2995_, lean_object* v_b_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2992_, v_as_2993_, v_sz_2994_, v_i_2995_, v_b_2996_);
return v___x_3002_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2992_ = stack[0].m_obj;
lean_object* v_as_2993_ = stack[1].m_obj;
size_t v_sz_2994_ = stack[2].m_num;
size_t v_i_2995_ = stack[3].m_num;
lean_object* v_b_2996_ = stack[4].m_obj;
lean_object* v___y_2997_ = stack[5].m_obj;
lean_object* v___y_2998_ = stack[6].m_obj;
lean_object* v___y_2999_ = stack[7].m_obj;
lean_object* v___y_3000_ = stack[8].m_obj;
lean_object* v_res_3003_;
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2992_, v_as_2993_, v_sz_2994_, v_i_2995_, v_b_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
stack->m_obj
 = v_res_3003_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_3004_, lean_object* v_as_3005_, lean_object* v_sz_3006_, lean_object* v_i_3007_, lean_object* v_b_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3006_);
lean_dec(v_sz_3006_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3007_);
lean_dec(v_i_3007_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_3004_, v_as_3005_, v_sz_boxed_3014_, v_i_boxed_3015_, v_b_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_as_3005_);
lean_dec_ref(v_a_3004_);
return v_res_3016_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_3017_, lean_object* v_a_3018_, lean_object* v_x_3019_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_3018_, v_x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3018_ = stack[1].m_obj;
lean_object* v_x_3019_ = stack[2].m_obj;
uint8_t v_res_3021_;
v_res_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_box(0), v_a_3018_, v_x_3019_);
stack->m_num = v_res_3021_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_3022_, lean_object* v_a_3023_, lean_object* v_x_3024_){
_start:
{
uint8_t v_res_3025_; lean_object* v_r_3026_; 
v_res_3025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_3022_, v_a_3023_, v_x_3024_);
lean_dec(v_x_3024_);
lean_dec_ref(v_a_3023_);
v_r_3026_ = lean_box(v_res_3025_);
return v_r_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_3027_, lean_object* v_data_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_3030_, lean_object* v_i_3031_, lean_object* v_source_3032_, lean_object* v_target_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_3031_, v_source_3032_, v_target_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_3035_, lean_object* v_x_3036_, lean_object* v_x_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_3036_, v_x_3037_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = l_Lean_maxRecDepthErrorMessage;
v___x_3045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_3047_ = l_Lean_MessageData_ofFormat(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_3049_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_3050_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_3048_);
return v___x_3050_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_3051_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v_ref_3051_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3051_ = stack[0].m_obj;
lean_object* v_res_3056_;
v_res_3056_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3051_);
stack->m_obj
 = v_res_3056_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3057_);
return v_res_3059_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_3060_, lean_object* v_ref_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3061_);
return v___x_3068_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3061_ = stack[1].m_obj;
lean_object* v___y_3062_ = stack[2].m_obj;
lean_object* v___y_3063_ = stack[3].m_obj;
lean_object* v___y_3064_ = stack[4].m_obj;
lean_object* v___y_3065_ = stack[5].m_obj;
lean_object* v___y_3066_ = stack[6].m_obj;
lean_object* v_res_3069_;
v_res_3069_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_box(0), v_ref_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
stack->m_obj
 = v_res_3069_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_ref_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_3070_, v_ref_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
return v_res_3078_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_3079_, lean_object* v_mvarId_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_toCold_3087_; lean_object* v_currRecDepth_3088_; lean_object* v_ref_3089_; uint16_t v_optionFlags_3090_; uint8_t v_suppressElabErrors_3091_; uint8_t v_isRecordingDeps_3092_; lean_object* v_maxRecDepth_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v_toCold_3087_ = lean_ctor_get(v_a_3084_, 0);
v_currRecDepth_3088_ = lean_ctor_get(v_a_3084_, 1);
v_ref_3089_ = lean_ctor_get(v_a_3084_, 2);
v_optionFlags_3090_ = lean_ctor_get_uint16(v_a_3084_, sizeof(void*)*3);
v_suppressElabErrors_3091_ = lean_ctor_get_uint8(v_a_3084_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3092_ = lean_ctor_get_uint8(v_a_3084_, sizeof(void*)*3 + 3);
v_maxRecDepth_3120_ = lean_ctor_get(v_toCold_3087_, 3);
v___x_3121_ = lean_unsigned_to_nat(0u);
v___x_3122_ = lean_nat_dec_eq(v_maxRecDepth_3120_, v___x_3121_);
if (v___x_3122_ == 0)
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_nat_dec_eq(v_currRecDepth_3088_, v_maxRecDepth_3120_);
if (v___x_3123_ == 0)
{
goto v___jp_3093_;
}
else
{
lean_object* v___x_3124_; 
lean_dec(v_mvarId_3080_);
lean_dec_ref(v_x_3079_);
lean_inc(v_ref_3089_);
v___x_3124_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3089_);
return v___x_3124_;
}
}
else
{
goto v___jp_3093_;
}
v___jp_3093_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_nat_add(v_currRecDepth_3088_, v___x_3094_);
lean_inc(v_ref_3089_);
lean_inc_ref(v_toCold_3087_);
v___x_3096_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3096_, 0, v_toCold_3087_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
lean_ctor_set(v___x_3096_, 2, v_ref_3089_);
lean_ctor_set_uint16(v___x_3096_, sizeof(void*)*3, v_optionFlags_3090_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*3 + 2, v_suppressElabErrors_3091_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*3 + 3, v_isRecordingDeps_3092_);
lean_inc_ref(v_x_3079_);
lean_inc(v_a_3085_);
lean_inc_ref(v___x_3096_);
lean_inc(v_a_3083_);
lean_inc_ref(v_a_3082_);
lean_inc(v_mvarId_3080_);
v___x_3097_ = lean_apply_6(v_x_3079_, v_mvarId_3080_, v_a_3082_, v_a_3083_, v___x_3096_, v_a_3085_, lean_box(0));
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3111_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3111_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3111_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
if (lean_obj_tag(v_a_3098_) == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_dec_ref_known(v___x_3096_, 3);
lean_dec_ref(v_x_3079_);
v___x_3102_ = lean_st_ref_take(v_a_3081_);
v___x_3103_ = lean_box(0);
v___x_3104_ = lean_array_push(v___x_3102_, v_mvarId_3080_);
v___x_3105_ = lean_st_ref_put(v_a_3081_, v___x_3104_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3103_);
v___x_3107_ = v___x_3100_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3103_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
else
{
lean_object* v_val_3109_; lean_object* v___x_3110_; 
lean_del_object(v___x_3100_);
lean_dec(v_mvarId_3080_);
v_val_3109_ = lean_ctor_get(v_a_3098_, 0);
lean_inc(v_val_3109_);
lean_dec_ref_known(v_a_3098_, 1);
v___x_3110_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3079_, v_val_3109_, v_a_3081_, v_a_3082_, v_a_3083_, v___x_3096_, v_a_3085_);
lean_dec_ref_known(v___x_3096_, 3);
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref_known(v___x_3096_, 3);
lean_dec(v_mvarId_3080_);
lean_dec_ref(v_x_3079_);
v_a_3112_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3097_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3097_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3079_ = stack[0].m_obj;
lean_object* v_mvarId_3080_ = stack[1].m_obj;
lean_object* v_a_3081_ = stack[2].m_obj;
lean_object* v_a_3082_ = stack[3].m_obj;
lean_object* v_a_3083_ = stack[4].m_obj;
lean_object* v_a_3084_ = stack[5].m_obj;
lean_object* v_a_3085_ = stack[6].m_obj;
lean_object* v_res_3125_;
v_res_3125_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3079_, v_mvarId_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
stack->m_obj
 = v_res_3125_;
}
lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3126_, lean_object* v_as_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
if (lean_obj_tag(v_as_3127_) == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_x_3126_);
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v_head_3136_; lean_object* v_tail_3137_; lean_object* v___x_3138_; 
v_head_3136_ = lean_ctor_get(v_as_3127_, 0);
lean_inc(v_head_3136_);
v_tail_3137_ = lean_ctor_get(v_as_3127_, 1);
lean_inc(v_tail_3137_);
lean_dec_ref_known(v_as_3127_, 2);
lean_inc_ref(v_x_3126_);
v___x_3138_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3126_, v_head_3136_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_dec_ref_known(v___x_3138_, 1);
v_as_3127_ = v_tail_3137_;
goto _start;
}
else
{
lean_dec(v_tail_3137_);
lean_dec_ref(v_x_3126_);
return v___x_3138_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3126_ = stack[0].m_obj;
lean_object* v_as_3127_ = stack[1].m_obj;
lean_object* v___y_3128_ = stack[2].m_obj;
lean_object* v___y_3129_ = stack[3].m_obj;
lean_object* v___y_3130_ = stack[4].m_obj;
lean_object* v___y_3131_ = stack[5].m_obj;
lean_object* v___y_3132_ = stack[6].m_obj;
lean_object* v_res_3140_;
v_res_3140_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3126_, v_as_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
stack->m_obj
 = v_res_3140_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3141_, lean_object* v_as_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3141_, v_as_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3150_, lean_object* v_mvarId_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3150_, v_mvarId_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
return v_res_3158_;
}
}
lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3159_, lean_object* v_x_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3167_ = lean_st_mk_ref(v___x_3166_);
v___x_3168_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3160_, v_mvarId_3159_, v___x_3167_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3177_; 
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v___x_3168_, 0);
lean_dec(v_unused_3178_);
v___x_3170_ = v___x_3168_;
v_isShared_3171_ = v_isSharedCheck_3177_;
goto v_resetjp_3169_;
}
else
{
lean_dec(v___x_3168_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3177_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3172_ = lean_st_ref_get(v___x_3167_);
lean_dec(v___x_3167_);
v___x_3173_ = lean_array_to_list(v___x_3172_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v___x_3173_);
v___x_3175_ = v___x_3170_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v___x_3167_);
v_a_3179_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3168_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3168_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_saturate_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3159_ = stack[0].m_obj;
lean_object* v_x_3160_ = stack[1].m_obj;
lean_object* v_a_3161_ = stack[2].m_obj;
lean_object* v_a_3162_ = stack[3].m_obj;
lean_object* v_a_3163_ = stack[4].m_obj;
lean_object* v_a_3164_ = stack[5].m_obj;
lean_object* v_res_3187_;
v_res_3187_ = l_Lean_Meta_saturate(v_mvarId_3159_, v_x_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_);
stack->m_obj
 = v_res_3187_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3188_, lean_object* v_x_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Meta_saturate(v_mvarId_3188_, v_x_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
return v_res_3195_;
}
}
lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3196_, lean_object* v_msg_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
if (lean_obj_tag(v_mvarIds_3196_) == 1)
{
lean_object* v_tail_3203_; 
v_tail_3203_ = lean_ctor_get(v_mvarIds_3196_, 1);
if (lean_obj_tag(v_tail_3203_) == 0)
{
lean_object* v_head_3204_; lean_object* v___x_3205_; 
lean_dec_ref(v_msg_3197_);
v_head_3204_ = lean_ctor_get(v_mvarIds_3196_, 0);
lean_inc(v_head_3204_);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_head_3204_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
return v___x_3206_;
}
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
return v___x_3207_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_exactlyOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarIds_3196_ = stack[0].m_obj;
lean_object* v_msg_3197_ = stack[1].m_obj;
lean_object* v_a_3198_ = stack[2].m_obj;
lean_object* v_a_3199_ = stack[3].m_obj;
lean_object* v_a_3200_ = stack[4].m_obj;
lean_object* v_a_3201_ = stack[5].m_obj;
lean_object* v_res_3208_;
v_res_3208_ = l_Lean_Meta_exactlyOne(v_mvarIds_3196_, v_msg_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
stack->m_obj
 = v_res_3208_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3209_, lean_object* v_msg_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Meta_exactlyOne(v_mvarIds_3209_, v_msg_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_mvarIds_3209_);
return v_res_3216_;
}
}
lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3217_, lean_object* v_msg_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
if (lean_obj_tag(v_mvarIds_3217_) == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec_ref(v_msg_3218_);
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
return v___x_3225_;
}
else
{
lean_object* v_tail_3226_; 
v_tail_3226_ = lean_ctor_get(v_mvarIds_3217_, 1);
if (lean_obj_tag(v_tail_3226_) == 0)
{
lean_object* v_head_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_dec_ref(v_msg_3218_);
v_head_3227_ = lean_ctor_get(v_mvarIds_3217_, 0);
lean_inc(v_head_3227_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_head_3227_);
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
return v___x_3230_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_ensureAtMostOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarIds_3217_ = stack[0].m_obj;
lean_object* v_msg_3218_ = stack[1].m_obj;
lean_object* v_a_3219_ = stack[2].m_obj;
lean_object* v_a_3220_ = stack[3].m_obj;
lean_object* v_a_3221_ = stack[4].m_obj;
lean_object* v_a_3222_ = stack[5].m_obj;
lean_object* v_res_3231_;
v_res_3231_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3217_, v_msg_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
stack->m_obj
 = v_res_3231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3232_, lean_object* v_msg_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3232_, v_msg_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_mvarIds_3232_);
return v_res_3239_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3240_, size_t v_sz_3241_, size_t v_i_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_usize_dec_lt(v_i_3242_, v_sz_3241_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_b_3243_);
return v___x_3250_;
}
else
{
lean_object* v_snd_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3281_; 
v_snd_3251_ = lean_ctor_get(v_b_3243_, 1);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_b_3243_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_b_3243_, 0);
lean_dec(v_unused_3282_);
v___x_3253_ = v_b_3243_;
v_isShared_3254_ = v_isSharedCheck_3281_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_snd_3251_);
lean_dec(v_b_3243_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3281_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v_a_3257_; lean_object* v_a_3264_; 
v___x_3255_ = lean_box(0);
v_a_3264_ = lean_array_uget_borrowed(v_as_3240_, v_i_3242_);
if (lean_obj_tag(v_a_3264_) == 0)
{
v_a_3257_ = v_snd_3251_;
goto v___jp_3256_;
}
else
{
lean_object* v_val_3265_; uint8_t v___x_3266_; 
v_val_3265_ = lean_ctor_get(v_a_3264_, 0);
v___x_3266_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = l_Lean_LocalDecl_type(v_val_3265_);
v___x_3268_ = l_Lean_Meta_isProp(v___x_3267_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; uint8_t v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = lean_unbox(v_a_3269_);
lean_dec(v_a_3269_);
if (v___x_3270_ == 0)
{
v_a_3257_ = v_snd_3251_;
goto v___jp_3256_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = l_Lean_LocalDecl_fvarId(v_val_3265_);
v___x_3272_ = lean_array_push(v_snd_3251_, v___x_3271_);
v_a_3257_ = v___x_3272_;
goto v___jp_3256_;
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_del_object(v___x_3253_);
lean_dec(v_snd_3251_);
v_a_3273_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3268_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3268_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
else
{
v_a_3257_ = v_snd_3251_;
goto v___jp_3256_;
}
}
v___jp_3256_:
{
lean_object* v___x_3259_; 
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v_a_3257_);
lean_ctor_set(v___x_3253_, 0, v___x_3255_);
v___x_3259_ = v___x_3253_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_a_3257_);
v___x_3259_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
size_t v___x_3260_; size_t v___x_3261_; 
v___x_3260_ = ((size_t)1ULL);
v___x_3261_ = lean_usize_add(v_i_3242_, v___x_3260_);
v_i_3242_ = v___x_3261_;
v_b_3243_ = v___x_3259_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3240_ = stack[0].m_obj;
size_t v_sz_3241_ = stack[1].m_num;
size_t v_i_3242_ = stack[2].m_num;
lean_object* v_b_3243_ = stack[3].m_obj;
lean_object* v___y_3244_ = stack[4].m_obj;
lean_object* v___y_3245_ = stack[5].m_obj;
lean_object* v___y_3246_ = stack[6].m_obj;
lean_object* v___y_3247_ = stack[7].m_obj;
lean_object* v_res_3283_;
v_res_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3240_, v_sz_3241_, v_i_3242_, v_b_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
stack->m_obj
 = v_res_3283_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3284_, lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
size_t v_sz_boxed_3293_; size_t v_i_boxed_3294_; lean_object* v_res_3295_; 
v_sz_boxed_3293_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3294_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3284_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec_ref(v_as_3284_);
return v_res_3295_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3296_, size_t v_sz_3297_, size_t v_i_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_usize_dec_lt(v_i_3298_, v_sz_3297_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_b_3299_);
return v___x_3306_;
}
else
{
lean_object* v_snd_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3337_; 
v_snd_3307_ = lean_ctor_get(v_b_3299_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_b_3299_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v_b_3299_, 0);
lean_dec(v_unused_3338_);
v___x_3309_ = v_b_3299_;
v_isShared_3310_ = v_isSharedCheck_3337_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_snd_3307_);
lean_dec(v_b_3299_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3337_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v_a_3313_; lean_object* v_a_3320_; 
v___x_3311_ = lean_box(0);
v_a_3320_ = lean_array_uget_borrowed(v_as_3296_, v_i_3298_);
if (lean_obj_tag(v_a_3320_) == 0)
{
v_a_3313_ = v_snd_3307_;
goto v___jp_3312_;
}
else
{
lean_object* v_val_3321_; uint8_t v___x_3322_; 
v_val_3321_ = lean_ctor_get(v_a_3320_, 0);
v___x_3322_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = l_Lean_LocalDecl_type(v_val_3321_);
v___x_3324_ = l_Lean_Meta_isProp(v___x_3323_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; uint8_t v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3326_ = lean_unbox(v_a_3325_);
lean_dec(v_a_3325_);
if (v___x_3326_ == 0)
{
v_a_3313_ = v_snd_3307_;
goto v___jp_3312_;
}
else
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = l_Lean_LocalDecl_fvarId(v_val_3321_);
v___x_3328_ = lean_array_push(v_snd_3307_, v___x_3327_);
v_a_3313_ = v___x_3328_;
goto v___jp_3312_;
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_del_object(v___x_3309_);
lean_dec(v_snd_3307_);
v_a_3329_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3324_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3324_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
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
else
{
v_a_3313_ = v_snd_3307_;
goto v___jp_3312_;
}
}
v___jp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v_a_3313_);
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3315_ = v___x_3309_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_a_3313_);
v___x_3315_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
size_t v___x_3316_; size_t v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = ((size_t)1ULL);
v___x_3317_ = lean_usize_add(v_i_3298_, v___x_3316_);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3296_, v_sz_3297_, v___x_3317_, v___x_3315_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
return v___x_3318_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3296_ = stack[0].m_obj;
size_t v_sz_3297_ = stack[1].m_num;
size_t v_i_3298_ = stack[2].m_num;
lean_object* v_b_3299_ = stack[3].m_obj;
lean_object* v___y_3300_ = stack[4].m_obj;
lean_object* v___y_3301_ = stack[5].m_obj;
lean_object* v___y_3302_ = stack[6].m_obj;
lean_object* v___y_3303_ = stack[7].m_obj;
lean_object* v_res_3339_;
v_res_3339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3296_, v_sz_3297_, v_i_3298_, v_b_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
stack->m_obj
 = v_res_3339_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3340_, lean_object* v_sz_3341_, lean_object* v_i_3342_, lean_object* v_b_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
size_t v_sz_boxed_3349_; size_t v_i_boxed_3350_; lean_object* v_res_3351_; 
v_sz_boxed_3349_ = lean_unbox_usize(v_sz_3341_);
lean_dec(v_sz_3341_);
v_i_boxed_3350_ = lean_unbox_usize(v_i_3342_);
lean_dec(v_i_3342_);
v_res_3351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3340_, v_sz_boxed_3349_, v_i_boxed_3350_, v_b_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec_ref(v_as_3340_);
return v_res_3351_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3352_, lean_object* v_n_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
if (lean_obj_tag(v_n_3353_) == 0)
{
lean_object* v_cs_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; size_t v_sz_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v_cs_3360_ = lean_ctor_get(v_n_3353_, 0);
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v_b_3354_);
v_sz_3363_ = lean_array_size(v_cs_3360_);
v___x_3364_ = ((size_t)0ULL);
v___x_3365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3352_, v_cs_3360_, v_sz_3363_, v___x_3364_, v___x_3362_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3380_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3380_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3380_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_fst_3370_; 
v_fst_3370_ = lean_ctor_get(v_a_3366_, 0);
if (lean_obj_tag(v_fst_3370_) == 0)
{
lean_object* v_snd_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v_snd_3371_ = lean_ctor_get(v_a_3366_, 1);
lean_inc(v_snd_3371_);
lean_dec(v_a_3366_);
v___x_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_snd_3371_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v___x_3372_);
v___x_3374_ = v___x_3368_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3378_; 
lean_inc_ref(v_fst_3370_);
lean_dec(v_a_3366_);
v_val_3376_ = lean_ctor_get(v_fst_3370_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v_fst_3370_, 1);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v_val_3376_);
v___x_3378_ = v___x_3368_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_val_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_a_3381_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3365_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3365_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v_vs_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; size_t v_sz_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v_vs_3389_ = lean_ctor_get(v_n_3353_, 0);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v_b_3354_);
v_sz_3392_ = lean_array_size(v_vs_3389_);
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3389_, v_sz_3392_, v___x_3393_, v___x_3391_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3409_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3409_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3409_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_fst_3399_; 
v_fst_3399_ = lean_ctor_get(v_a_3395_, 0);
if (lean_obj_tag(v_fst_3399_) == 0)
{
lean_object* v_snd_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v_snd_3400_ = lean_ctor_get(v_a_3395_, 1);
lean_inc(v_snd_3400_);
lean_dec(v_a_3395_);
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v_snd_3400_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3401_);
v___x_3403_ = v___x_3397_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3407_; 
lean_inc_ref(v_fst_3399_);
lean_dec(v_a_3395_);
v_val_3405_ = lean_ctor_get(v_fst_3399_, 0);
lean_inc(v_val_3405_);
lean_dec_ref_known(v_fst_3399_, 1);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v_val_3405_);
v___x_3407_ = v___x_3397_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_val_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v_a_3410_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3394_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3394_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3352_ = stack[0].m_obj;
lean_object* v_n_3353_ = stack[1].m_obj;
lean_object* v_b_3354_ = stack[2].m_obj;
lean_object* v___y_3355_ = stack[3].m_obj;
lean_object* v___y_3356_ = stack[4].m_obj;
lean_object* v___y_3357_ = stack[5].m_obj;
lean_object* v___y_3358_ = stack[6].m_obj;
lean_object* v_res_3418_;
v_res_3418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3352_, v_n_3353_, v_b_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
stack->m_obj
 = v_res_3418_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3419_, lean_object* v_as_3420_, size_t v_sz_3421_, size_t v_i_3422_, lean_object* v_b_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v___x_3429_; 
v___x_3429_ = lean_usize_dec_lt(v_i_3422_, v_sz_3421_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_b_3423_);
return v___x_3430_;
}
else
{
lean_object* v_snd_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3465_; 
v_snd_3431_ = lean_ctor_get(v_b_3423_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_b_3423_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_b_3423_, 0);
lean_dec(v_unused_3466_);
v___x_3433_ = v_b_3423_;
v_isShared_3434_ = v_isSharedCheck_3465_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_snd_3431_);
lean_dec(v_b_3423_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3465_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v_a_3436_; lean_object* v___x_3437_; 
v___x_3435_ = lean_box(0);
v_a_3436_ = lean_array_uget_borrowed(v_as_3420_, v_i_3422_);
lean_inc(v_snd_3431_);
v___x_3437_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3419_, v_a_3436_, v_snd_3431_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3456_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3456_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3456_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
if (lean_obj_tag(v_a_3438_) == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v_a_3438_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3442_);
v___x_3444_ = v___x_3433_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_snd_3431_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3444_);
v___x_3446_ = v___x_3440_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; 
lean_del_object(v___x_3440_);
lean_dec(v_snd_3431_);
v_a_3449_ = lean_ctor_get(v_a_3438_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v_a_3438_, 1);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v_a_3449_);
lean_ctor_set(v___x_3433_, 0, v___x_3435_);
v___x_3451_ = v___x_3433_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_a_3449_);
v___x_3451_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
size_t v___x_3452_; size_t v___x_3453_; 
v___x_3452_ = ((size_t)1ULL);
v___x_3453_ = lean_usize_add(v_i_3422_, v___x_3452_);
v_i_3422_ = v___x_3453_;
v_b_3423_ = v___x_3451_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_del_object(v___x_3433_);
lean_dec(v_snd_3431_);
v_a_3457_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3437_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3437_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3419_ = stack[0].m_obj;
lean_object* v_as_3420_ = stack[1].m_obj;
size_t v_sz_3421_ = stack[2].m_num;
size_t v_i_3422_ = stack[3].m_num;
lean_object* v_b_3423_ = stack[4].m_obj;
lean_object* v___y_3424_ = stack[5].m_obj;
lean_object* v___y_3425_ = stack[6].m_obj;
lean_object* v___y_3426_ = stack[7].m_obj;
lean_object* v___y_3427_ = stack[8].m_obj;
lean_object* v_res_3467_;
v_res_3467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3419_, v_as_3420_, v_sz_3421_, v_i_3422_, v_b_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
stack->m_obj
 = v_res_3467_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3468_, lean_object* v_as_3469_, lean_object* v_sz_3470_, lean_object* v_i_3471_, lean_object* v_b_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3470_);
lean_dec(v_sz_3470_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3471_);
lean_dec(v_i_3471_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3468_, v_as_3469_, v_sz_boxed_3478_, v_i_boxed_3479_, v_b_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec_ref(v_as_3469_);
lean_dec_ref(v_init_3468_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3481_, lean_object* v_n_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3481_, v_n_3482_, v_b_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_n_3482_);
lean_dec_ref(v_init_3481_);
return v_res_3489_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3490_, size_t v_sz_3491_, size_t v_i_3492_, lean_object* v_b_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v___x_3499_; 
v___x_3499_ = lean_usize_dec_lt(v_i_3492_, v_sz_3491_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v_b_3493_);
return v___x_3500_;
}
else
{
lean_object* v_snd_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3531_; 
v_snd_3501_ = lean_ctor_get(v_b_3493_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_b_3493_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v_b_3493_, 0);
lean_dec(v_unused_3532_);
v___x_3503_ = v_b_3493_;
v_isShared_3504_ = v_isSharedCheck_3531_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snd_3501_);
lean_dec(v_b_3493_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3531_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v_a_3507_; lean_object* v_a_3514_; 
v___x_3505_ = lean_box(0);
v_a_3514_ = lean_array_uget_borrowed(v_as_3490_, v_i_3492_);
if (lean_obj_tag(v_a_3514_) == 0)
{
v_a_3507_ = v_snd_3501_;
goto v___jp_3506_;
}
else
{
lean_object* v_val_3515_; uint8_t v___x_3516_; 
v_val_3515_ = lean_ctor_get(v_a_3514_, 0);
v___x_3516_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = l_Lean_LocalDecl_type(v_val_3515_);
v___x_3518_ = l_Lean_Meta_isProp(v___x_3517_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; uint8_t v___x_3520_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v___x_3520_ = lean_unbox(v_a_3519_);
lean_dec(v_a_3519_);
if (v___x_3520_ == 0)
{
v_a_3507_ = v_snd_3501_;
goto v___jp_3506_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = l_Lean_LocalDecl_fvarId(v_val_3515_);
v___x_3522_ = lean_array_push(v_snd_3501_, v___x_3521_);
v_a_3507_ = v___x_3522_;
goto v___jp_3506_;
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_del_object(v___x_3503_);
lean_dec(v_snd_3501_);
v_a_3523_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3518_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3518_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
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
v_a_3507_ = v_snd_3501_;
goto v___jp_3506_;
}
}
v___jp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v_a_3507_);
lean_ctor_set(v___x_3503_, 0, v___x_3505_);
v___x_3509_ = v___x_3503_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_a_3507_);
v___x_3509_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
size_t v___x_3510_; size_t v___x_3511_; 
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_add(v_i_3492_, v___x_3510_);
v_i_3492_ = v___x_3511_;
v_b_3493_ = v___x_3509_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3490_ = stack[0].m_obj;
size_t v_sz_3491_ = stack[1].m_num;
size_t v_i_3492_ = stack[2].m_num;
lean_object* v_b_3493_ = stack[3].m_obj;
lean_object* v___y_3494_ = stack[4].m_obj;
lean_object* v___y_3495_ = stack[5].m_obj;
lean_object* v___y_3496_ = stack[6].m_obj;
lean_object* v___y_3497_ = stack[7].m_obj;
lean_object* v_res_3533_;
v_res_3533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3490_, v_sz_3491_, v_i_3492_, v_b_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
stack->m_obj
 = v_res_3533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3534_, lean_object* v_sz_3535_, lean_object* v_i_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
size_t v_sz_boxed_3543_; size_t v_i_boxed_3544_; lean_object* v_res_3545_; 
v_sz_boxed_3543_ = lean_unbox_usize(v_sz_3535_);
lean_dec(v_sz_3535_);
v_i_boxed_3544_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3534_, v_sz_boxed_3543_, v_i_boxed_3544_, v_b_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v_as_3534_);
return v_res_3545_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3546_, size_t v_sz_3547_, size_t v_i_3548_, lean_object* v_b_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v___x_3555_; 
v___x_3555_ = lean_usize_dec_lt(v_i_3548_, v_sz_3547_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_b_3549_);
return v___x_3556_;
}
else
{
lean_object* v_snd_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3587_; 
v_snd_3557_ = lean_ctor_get(v_b_3549_, 1);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_b_3549_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v_b_3549_, 0);
lean_dec(v_unused_3588_);
v___x_3559_ = v_b_3549_;
v_isShared_3560_ = v_isSharedCheck_3587_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snd_3557_);
lean_dec(v_b_3549_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3587_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v_a_3563_; lean_object* v_a_3570_; 
v___x_3561_ = lean_box(0);
v_a_3570_ = lean_array_uget_borrowed(v_as_3546_, v_i_3548_);
if (lean_obj_tag(v_a_3570_) == 0)
{
v_a_3563_ = v_snd_3557_;
goto v___jp_3562_;
}
else
{
lean_object* v_val_3571_; uint8_t v___x_3572_; 
v_val_3571_ = lean_ctor_get(v_a_3570_, 0);
v___x_3572_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = l_Lean_LocalDecl_type(v_val_3571_);
v___x_3574_ = l_Lean_Meta_isProp(v___x_3573_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; uint8_t v___x_3576_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3576_ = lean_unbox(v_a_3575_);
lean_dec(v_a_3575_);
if (v___x_3576_ == 0)
{
v_a_3563_ = v_snd_3557_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = l_Lean_LocalDecl_fvarId(v_val_3571_);
v___x_3578_ = lean_array_push(v_snd_3557_, v___x_3577_);
v_a_3563_ = v___x_3578_;
goto v___jp_3562_;
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_del_object(v___x_3559_);
lean_dec(v_snd_3557_);
v_a_3579_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3574_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3574_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
v_a_3563_ = v_snd_3557_;
goto v___jp_3562_;
}
}
v___jp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v_a_3563_);
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3565_ = v___x_3559_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_a_3563_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
size_t v___x_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((size_t)1ULL);
v___x_3567_ = lean_usize_add(v_i_3548_, v___x_3566_);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3546_, v_sz_3547_, v___x_3567_, v___x_3565_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
return v___x_3568_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3546_ = stack[0].m_obj;
size_t v_sz_3547_ = stack[1].m_num;
size_t v_i_3548_ = stack[2].m_num;
lean_object* v_b_3549_ = stack[3].m_obj;
lean_object* v___y_3550_ = stack[4].m_obj;
lean_object* v___y_3551_ = stack[5].m_obj;
lean_object* v___y_3552_ = stack[6].m_obj;
lean_object* v___y_3553_ = stack[7].m_obj;
lean_object* v_res_3589_;
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3546_, v_sz_3547_, v_i_3548_, v_b_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
stack->m_obj
 = v_res_3589_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3590_, lean_object* v_sz_3591_, lean_object* v_i_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
size_t v_sz_boxed_3599_; size_t v_i_boxed_3600_; lean_object* v_res_3601_; 
v_sz_boxed_3599_ = lean_unbox_usize(v_sz_3591_);
lean_dec(v_sz_3591_);
v_i_boxed_3600_ = lean_unbox_usize(v_i_3592_);
lean_dec(v_i_3592_);
v_res_3601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3590_, v_sz_boxed_3599_, v_i_boxed_3600_, v_b_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_as_3590_);
return v_res_3601_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3602_, lean_object* v_init_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_root_3609_; lean_object* v_tail_3610_; lean_object* v___x_3611_; 
v_root_3609_ = lean_ctor_get(v_t_3602_, 0);
v_tail_3610_ = lean_ctor_get(v_t_3602_, 1);
lean_inc_ref(v_init_3603_);
v___x_3611_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3603_, v_root_3609_, v_init_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec_ref(v_init_3603_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3648_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3648_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3648_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
if (lean_obj_tag(v_a_3612_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; 
v_a_3616_ = lean_ctor_get(v_a_3612_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v_a_3612_, 1);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 0, v_a_3616_);
v___x_3618_ = v___x_3614_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3616_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; size_t v_sz_3623_; size_t v___x_3624_; lean_object* v___x_3625_; 
lean_del_object(v___x_3614_);
v_a_3620_ = lean_ctor_get(v_a_3612_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v_a_3612_, 1);
v___x_3621_ = lean_box(0);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v_a_3620_);
v_sz_3623_ = lean_array_size(v_tail_3610_);
v___x_3624_ = ((size_t)0ULL);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3610_, v_sz_3623_, v___x_3624_, v___x_3622_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3639_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3639_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3639_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v_fst_3630_; 
v_fst_3630_ = lean_ctor_get(v_a_3626_, 0);
if (lean_obj_tag(v_fst_3630_) == 0)
{
lean_object* v_snd_3631_; lean_object* v___x_3633_; 
v_snd_3631_ = lean_ctor_get(v_a_3626_, 1);
lean_inc(v_snd_3631_);
lean_dec(v_a_3626_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v_snd_3631_);
v___x_3633_ = v___x_3628_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_snd_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
else
{
lean_object* v_val_3635_; lean_object* v___x_3637_; 
lean_inc_ref(v_fst_3630_);
lean_dec(v_a_3626_);
v_val_3635_ = lean_ctor_get(v_fst_3630_, 0);
lean_inc(v_val_3635_);
lean_dec_ref_known(v_fst_3630_, 1);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v_val_3635_);
v___x_3637_ = v___x_3628_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_val_3635_);
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
v_a_3640_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3625_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3625_);
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
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
v_a_3649_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3611_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3611_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3602_ = stack[0].m_obj;
lean_object* v_init_3603_ = stack[1].m_obj;
lean_object* v___y_3604_ = stack[2].m_obj;
lean_object* v___y_3605_ = stack[3].m_obj;
lean_object* v___y_3606_ = stack[4].m_obj;
lean_object* v___y_3607_ = stack[5].m_obj;
lean_object* v_res_3657_;
v_res_3657_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3602_, v_init_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
stack->m_obj
 = v_res_3657_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3658_, lean_object* v_init_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3658_, v_init_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec_ref(v_t_3658_);
return v_res_3665_;
}
}
lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_lctx_3671_; lean_object* v_decls_3672_; lean_object* v_result_3673_; lean_object* v___x_3674_; 
v_lctx_3671_ = lean_ctor_get(v_a_3666_, 2);
v_decls_3672_ = lean_ctor_get(v_lctx_3671_, 1);
v_result_3673_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3674_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3672_, v_result_3673_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
return v___x_3674_;
}
}
LEAN_EXPORT void l_Lean_Meta_getPropHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3666_ = stack[0].m_obj;
lean_object* v_a_3667_ = stack[1].m_obj;
lean_object* v_a_3668_ = stack[2].m_obj;
lean_object* v_a_3669_ = stack[3].m_obj;
lean_object* v_res_3675_;
v_res_3675_ = l_Lean_Meta_getPropHyps(v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
stack->m_obj
 = v_res_3675_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Meta_getPropHyps(v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_a_3677_);
lean_dec_ref(v_a_3676_);
return v_res_3681_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3686_ = l_Lean_MessageData_ofFormat(v___x_3685_);
return v___x_3686_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
}
lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3689_, lean_object* v___x_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___x_3696_; 
lean_inc(v___x_3690_);
lean_inc(v_mvarId_3689_);
v___x_3696_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3689_, v___x_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v___x_3697_; 
lean_dec_ref_known(v___x_3696_, 1);
lean_inc(v_mvarId_3689_);
v___x_3697_ = l_Lean_MVarId_getType(v_mvarId_3689_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3697_, 1);
v___x_3699_ = lean_box(0);
v___x_3700_ = l_Lean_Meta_synthInstance(v_a_3698_, v___x_3699_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
lean_inc(v_mvarId_3689_);
v___x_3702_ = l_Lean_mkMVar(v_mvarId_3689_);
v___x_3703_ = l_Lean_Meta_isExprDefEq(v___x_3702_, v_a_3701_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3715_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3706_ = v___x_3703_;
v_isShared_3707_ = v_isSharedCheck_3715_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3703_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3715_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
uint8_t v___x_3708_; 
v___x_3708_ = lean_unbox(v_a_3704_);
lean_dec(v_a_3704_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_del_object(v___x_3706_);
v___x_3709_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3710_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3690_, v_mvarId_3689_, v___x_3709_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
lean_dec(v___x_3690_);
lean_dec(v_mvarId_3689_);
v___x_3711_ = lean_box(0);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3711_);
v___x_3713_ = v___x_3706_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v___x_3690_);
lean_dec(v_mvarId_3689_);
v_a_3716_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3703_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3703_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v___x_3690_);
lean_dec(v_mvarId_3689_);
v_a_3724_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3700_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3700_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v___x_3690_);
lean_dec(v_mvarId_3689_);
v_a_3732_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3697_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3697_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_dec(v___x_3690_);
lean_dec(v_mvarId_3689_);
return v___x_3696_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_inferInstance___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3689_ = stack[0].m_obj;
lean_object* v___x_3690_ = stack[1].m_obj;
lean_object* v___y_3691_ = stack[2].m_obj;
lean_object* v___y_3692_ = stack[3].m_obj;
lean_object* v___y_3693_ = stack[4].m_obj;
lean_object* v___y_3694_ = stack[5].m_obj;
lean_object* v_res_3740_;
v_res_3740_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3689_, v___x_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
stack->m_obj
 = v_res_3740_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3741_, lean_object* v___x_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3741_, v___x_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
return v_res_3748_;
}
}
lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_){
_start:
{
lean_object* v___x_3758_; lean_object* v___f_3759_; lean_object* v___x_3760_; 
v___x_3758_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3752_);
v___f_3759_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3759_, 0, v_mvarId_3752_);
lean_closure_set(v___f_3759_, 1, v___x_3758_);
v___x_3760_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3752_, v___f_3759_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_);
return v___x_3760_;
}
}
LEAN_EXPORT void l_Lean_MVarId_inferInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3752_ = stack[0].m_obj;
lean_object* v_a_3753_ = stack[1].m_obj;
lean_object* v_a_3754_ = stack[2].m_obj;
lean_object* v_a_3755_ = stack[3].m_obj;
lean_object* v_a_3756_ = stack[4].m_obj;
lean_object* v_res_3761_;
v_res_3761_ = l_Lean_MVarId_inferInstance(v_mvarId_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_);
stack->m_obj
 = v_res_3761_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_MVarId_inferInstance(v_mvarId_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl(lean_object* v_x_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_obj_tag_nat(v_x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl___boxed(lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Meta_TacticResultCNM_ctorIdx___impl(v_x_3771_);
lean_dec(v_x_3771_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3773_, lean_object* v_k_3774_){
_start:
{
if (lean_obj_tag(v_t_3773_) == 2)
{
lean_object* v_mvarId_3775_; lean_object* v___x_3776_; 
v_mvarId_3775_ = lean_ctor_get(v_t_3773_, 0);
lean_inc(v_mvarId_3775_);
lean_dec_ref_known(v_t_3773_, 1);
v___x_3776_ = lean_apply_1(v_k_3774_, v_mvarId_3775_);
return v___x_3776_;
}
else
{
lean_dec(v_t_3773_);
return v_k_3774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3777_, lean_object* v_ctorIdx_3778_, lean_object* v_t_3779_, lean_object* v_h_3780_, lean_object* v_k_3781_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3779_, v_k_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3783_, lean_object* v_ctorIdx_3784_, lean_object* v_t_3785_, lean_object* v_h_3786_, lean_object* v_k_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3783_, v_ctorIdx_3784_, v_t_3785_, v_h_3786_, v_k_3787_);
lean_dec(v_ctorIdx_3784_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3789_, lean_object* v_closed_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3789_, v_closed_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3792_, lean_object* v_t_3793_, lean_object* v_h_3794_, lean_object* v_closed_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3793_, v_closed_3795_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3797_, lean_object* v_noChange_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3797_, v_noChange_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3800_, lean_object* v_t_3801_, lean_object* v_h_3802_, lean_object* v_noChange_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3801_, v_noChange_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3805_, lean_object* v_modified_3806_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3805_, v_modified_3806_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3808_, lean_object* v_t_3809_, lean_object* v_h_3810_, lean_object* v_modified_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3809_, v_modified_3811_);
return v___x_3812_;
}
}
lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v___y_3823_; uint8_t v___y_3824_; lean_object* v_a_3829_; lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_MVarId_getType(v_g_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
v___x_3834_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = lean_mk_empty_array_with_capacity(v___x_3835_);
v___x_3837_ = lean_array_push(v___x_3836_, v_a_3833_);
v___x_3838_ = l_Lean_Meta_mkAppM(v___x_3834_, v___x_3837_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3840_ = lean_box(0);
v___x_3841_ = l_Lean_Meta_synthInstance(v_a_3839_, v___x_3840_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3850_; 
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v___x_3841_, 0);
lean_dec(v_unused_3851_);
v___x_3843_ = v___x_3841_;
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v___x_3841_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3850_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3845_ = 1;
v___x_3846_ = lean_box(v___x_3845_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3846_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
else
{
lean_object* v_a_3852_; 
v_a_3852_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3841_, 1);
v_a_3829_ = v_a_3852_;
goto v___jp_3828_;
}
}
else
{
lean_object* v_a_3853_; 
v_a_3853_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3838_, 1);
v_a_3829_ = v_a_3853_;
goto v___jp_3828_;
}
}
else
{
lean_object* v_a_3854_; 
v_a_3854_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3832_, 1);
v_a_3829_ = v_a_3854_;
goto v___jp_3828_;
}
v___jp_3822_:
{
if (v___y_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec_ref(v___y_3823_);
v___x_3825_ = lean_box(v___y_3824_);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___y_3823_);
return v___x_3827_;
}
}
v___jp_3828_:
{
uint8_t v___x_3830_; 
v___x_3830_ = l_Lean_Exception_isInterrupt(v_a_3829_);
if (v___x_3830_ == 0)
{
uint8_t v___x_3831_; 
lean_inc_ref(v_a_3829_);
v___x_3831_ = l_Lean_Exception_isRuntime(v_a_3829_);
v___y_3823_ = v_a_3829_;
v___y_3824_ = v___x_3831_;
goto v___jp_3822_;
}
else
{
v___y_3823_ = v_a_3829_;
v___y_3824_ = v___x_3830_;
goto v___jp_3822_;
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_isSubsingleton_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_3816_ = stack[0].m_obj;
lean_object* v_a_3817_ = stack[1].m_obj;
lean_object* v_a_3818_ = stack[2].m_obj;
lean_object* v_a_3819_ = stack[3].m_obj;
lean_object* v_a_3820_ = stack[4].m_obj;
lean_object* v_res_3855_;
v_res_3855_ = l_Lean_MVarId_isSubsingleton(v_g_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
stack->m_obj
 = v_res_3855_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_MVarId_isSubsingleton(v_g_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
return v_res_3862_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3883_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3880_, v___x_3881_, v___x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3884_;
v_res_3884_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
stack->m_obj
 = v_res_3884_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3886_;
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
