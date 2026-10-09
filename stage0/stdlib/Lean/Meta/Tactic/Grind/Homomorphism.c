// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Homomorphism
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.Simp.SimpM import Init.Grind.Homo.Extra import Lean.Meta.NatInstTesters import Lean.Meta.Sym.LitValues import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getHomoTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getHomoPredTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getHomoSourceTypes___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_Nat_mkInstHDiv;
extern lean_object* l_Lean_Nat_mkInstHMod;
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_mkNatSub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkHomoPredInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkEqMPCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hom"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 254, 229, 211, 186, 100, 148, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Homomorphism"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 40, 35, 7, 90, 245, 98, 206)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 33, 165, 246, 19, 142, 127, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 152, 96, 139, 215, 165, 231, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 88, 147, 154, 131, 237, 72, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 150, 207, 215, 57, 47, 128, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Homo"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 97, 15, 175, 123, 219, 173, 123)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 91, 45, 194, 122, 52, 201, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 55, 21, 223, 53, 32, 164, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 81, 60, 28, 4, 71, 132, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 152, 143, 143, 254, 232, 99, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(204, 80, 221, 141, 17, 69, 156, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 244, 64, 195, 64, 183, 126, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 30, 194, 254, 212, 12, 37, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pred"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 254, 229, 211, 186, 100, 148, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 94, 180, 116, 28, 106, 148, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_homExt;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "and_eq_div_mod_mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(172, 213, 253, 107, 196, 179, 180, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ones_zeros_and_eq_div_mod_mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(200, 71, 30, 242, 231, 136, 113, 27)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "and_eq_mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 150, 170, 114, 144, 96, 66, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ones_and_eq_mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(153, 240, 108, 217, 24, 169, 196, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "mul_mod_eq_sub_mul_mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 43, 118, 105, 221, 177, 248, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "mul_mod_eq_sub_mul_mod'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(41, 69, 29, 68, 4, 176, 204, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Homo_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Homo_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Homo_processNewDiseq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_unsigned_to_nat(3754153130u);
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_71_ = l_Lean_Name_num___override(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_75_ = l_Lean_Name_str___override(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_78_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_79_ = l_Lean_Name_str___override(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_82_ = l_Lean_Name_num___override(v___x_81_, v___x_80_);
return v___x_82_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_85_ = 0;
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_);
v___x_87_ = l_Lean_registerTraceClass(v___x_84_, v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_88_;
v_res_88_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
stack->m_obj
 = v_res_88_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2____boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
return v_res_90_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_unsigned_to_nat(2531264644u);
v___x_97_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_98_ = l_Lean_Name_num___override(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_101_ = l_Lean_Name_str___override(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_104_ = l_Lean_Name_str___override(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(2u);
v___x_106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_107_ = l_Lean_Name_num___override(v___x_106_, v___x_105_);
return v___x_107_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_110_ = 1;
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_112_ = l_Lean_registerTraceClass(v___x_109_, v___x_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_113_;
v_res_113_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2____boxed(lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
return v_res_115_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_116_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg(){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__1);
return v___x_120_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_121_;
v_res_121_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___dummy_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
return v_res_123_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg();
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0);
return v___x_126_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object* v___x_127_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
return v___x_129_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_127_ = stack[0].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(v___x_127_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v___x_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(v___x_131_);
return v_res_133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_138_ = l_Lean_NameSet_empty;
v___x_139_ = lean_box(1);
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_141_ = 0;
v___x_142_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0);
v___x_143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_144_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_142_);
lean_ctor_set(v___x_144_, 2, v___x_140_);
lean_ctor_set(v___x_144_, 3, v___x_139_);
lean_ctor_set(v___x_144_, 4, v___x_138_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*5, v___x_141_);
return v___x_144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_145_; lean_object* v___f_146_; 
v___x_145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___f_146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_146_, 0, v___x_145_);
return v___f_146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; 
v___f_148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_149_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_150_;
v_res_150_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
return v_res_152_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(uint8_t v___x_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_s_157_){
_start:
{
lean_object* v_cache_158_; lean_object* v_internalized_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_cache_158_ = lean_ctor_get(v_s_157_, 0);
v_internalized_159_ = lean_ctor_get(v_s_157_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_s_157_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; lean_object* v_unused_168_; lean_object* v_unused_169_; 
v_unused_167_ = lean_ctor_get(v_s_157_, 4);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_s_157_, 3);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_s_157_, 2);
lean_dec(v_unused_169_);
v___x_161_ = v_s_157_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_internalized_159_);
lean_inc(v_cache_158_);
lean_dec(v_s_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 4, v_a_156_);
lean_ctor_set(v___x_161_, 3, v_a_155_);
lean_ctor_set(v___x_161_, 2, v_a_154_);
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_cache_158_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_internalized_159_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_a_154_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_a_155_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v_a_156_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*5, v___x_153_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_153_ = stack[0].m_num;
lean_object* v_a_154_ = stack[1].m_obj;
lean_object* v_a_155_ = stack[2].m_obj;
lean_object* v_a_156_ = stack[3].m_obj;
lean_object* v_s_157_ = stack[4].m_obj;
lean_object* v_res_170_;
v_res_170_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(v___x_153_, v_a_154_, v_a_155_, v_a_156_, v_s_157_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed(lean_object* v___x_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_s_175_){
_start:
{
uint8_t v___x_4129__boxed_176_; lean_object* v_res_177_; 
v___x_4129__boxed_176_ = lean_unbox(v___x_171_);
v_res_177_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(v___x_4129__boxed_176_, v_a_172_, v_a_173_, v_a_174_, v_s_175_);
return v_res_177_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_183_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_182_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_227_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_227_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_227_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_227_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
uint8_t v_initialized_188_; 
v_initialized_188_ = lean_ctor_get_uint8(v_a_184_, sizeof(void*)*5);
lean_dec(v_a_184_);
if (v_initialized_188_ == 0)
{
uint8_t v___x_189_; lean_object* v___x_190_; 
lean_del_object(v___x_186_);
v___x_189_ = 1;
v___x_190_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_180_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_180_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_194_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_180_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = lean_box(v___x_189_);
v___f_197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_197_, 0, v___x_196_);
lean_closure_set(v___f_197_, 1, v_a_191_);
lean_closure_set(v___f_197_, 2, v_a_193_);
lean_closure_set(v___f_197_, 3, v_a_195_);
v___x_198_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_182_, v___f_197_, v_a_178_);
return v___x_198_;
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_193_);
lean_dec(v_a_191_);
v_a_199_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_194_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_194_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_a_191_);
v_a_207_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_192_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_192_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_a_215_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_190_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_190_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_box(0);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_223_);
v___x_225_ = v___x_186_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_183_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_183_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_178_ = stack[0].m_obj;
lean_object* v_a_179_ = stack[1].m_obj;
lean_object* v_a_180_ = stack[2].m_obj;
lean_object* v_res_236_;
v_res_236_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_178_, v_a_179_, v_a_180_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___boxed(lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
return v_res_241_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_242_, v_a_250_, v_a_251_);
return v___x_253_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_242_ = stack[0].m_obj;
lean_object* v_a_243_ = stack[1].m_obj;
lean_object* v_a_244_ = stack[2].m_obj;
lean_object* v_a_245_ = stack[3].m_obj;
lean_object* v_a_246_ = stack[4].m_obj;
lean_object* v_a_247_ = stack[5].m_obj;
lean_object* v_a_248_ = stack[6].m_obj;
lean_object* v_a_249_ = stack[7].m_obj;
lean_object* v_a_250_ = stack[8].m_obj;
lean_object* v_a_251_ = stack[9].m_obj;
lean_object* v_res_254_;
v_res_254_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___boxed(lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec(v_a_255_);
return v_res_266_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref_known(v___x_271_, 1);
v___x_272_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_273_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_272_, v_a_267_, v_a_268_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_thms_278_; lean_object* v___x_280_; 
v_thms_278_ = lean_ctor_get(v_a_274_, 2);
lean_inc_ref(v_thms_278_);
lean_dec(v_a_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_thms_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_thms_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_273_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_271_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_271_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_267_ = stack[0].m_obj;
lean_object* v_a_268_ = stack[1].m_obj;
lean_object* v_a_269_ = stack[2].m_obj;
lean_object* v_res_299_;
v_res_299_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_267_, v_a_268_, v_a_269_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg___boxed(lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
return v_res_304_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_305_, v_a_313_, v_a_314_);
return v___x_316_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_305_ = stack[0].m_obj;
lean_object* v_a_306_ = stack[1].m_obj;
lean_object* v_a_307_ = stack[2].m_obj;
lean_object* v_a_308_ = stack[3].m_obj;
lean_object* v_a_309_ = stack[4].m_obj;
lean_object* v_a_310_ = stack[5].m_obj;
lean_object* v_a_311_ = stack[6].m_obj;
lean_object* v_a_312_ = stack[7].m_obj;
lean_object* v_a_313_ = stack[8].m_obj;
lean_object* v_a_314_ = stack[9].m_obj;
lean_object* v_res_317_;
v_res_317_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___boxed(lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec(v_a_318_);
return v_res_329_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref_known(v___x_334_, 1);
v___x_335_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_336_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_335_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_345_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_preds_341_; lean_object* v___x_343_; 
v_preds_341_ = lean_ctor_get(v_a_337_, 3);
lean_inc(v_preds_341_);
lean_dec(v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v_preds_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_preds_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_336_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
v_a_354_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_334_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_334_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_330_ = stack[0].m_obj;
lean_object* v_a_331_ = stack[1].m_obj;
lean_object* v_a_332_ = stack[2].m_obj;
lean_object* v_res_362_;
v_res_362_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg___boxed(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
return v_res_367_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_368_, v_a_376_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_368_ = stack[0].m_obj;
lean_object* v_a_369_ = stack[1].m_obj;
lean_object* v_a_370_ = stack[2].m_obj;
lean_object* v_a_371_ = stack[3].m_obj;
lean_object* v_a_372_ = stack[4].m_obj;
lean_object* v_a_373_ = stack[5].m_obj;
lean_object* v_a_374_ = stack[6].m_obj;
lean_object* v_a_375_ = stack[7].m_obj;
lean_object* v_a_376_ = stack[8].m_obj;
lean_object* v_a_377_ = stack[9].m_obj;
lean_object* v_res_380_;
v_res_380_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___boxed(lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
return v_res_392_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref_known(v___x_397_, 1);
v___x_398_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_399_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_398_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_408_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_sourceTypes_404_; lean_object* v___x_406_; 
v_sourceTypes_404_ = lean_ctor_get(v_a_400_, 4);
lean_inc(v_sourceTypes_404_);
lean_dec(v_a_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_sourceTypes_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_sourceTypes_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_a_409_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_399_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_399_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_a_417_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_397_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_397_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_393_ = stack[0].m_obj;
lean_object* v_a_394_ = stack[1].m_obj;
lean_object* v_a_395_ = stack[2].m_obj;
lean_object* v_res_425_;
v_res_425_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_393_, v_a_394_, v_a_395_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg___boxed(lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
return v_res_430_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_431_, v_a_439_, v_a_440_);
return v___x_442_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_431_ = stack[0].m_obj;
lean_object* v_a_432_ = stack[1].m_obj;
lean_object* v_a_433_ = stack[2].m_obj;
lean_object* v_a_434_ = stack[3].m_obj;
lean_object* v_a_435_ = stack[4].m_obj;
lean_object* v_a_436_ = stack[5].m_obj;
lean_object* v_a_437_ = stack[6].m_obj;
lean_object* v_a_438_ = stack[7].m_obj;
lean_object* v_a_439_ = stack[8].m_obj;
lean_object* v_a_440_ = stack[9].m_obj;
lean_object* v_res_443_;
v_res_443_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___boxed(lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec(v_a_444_);
return v_res_455_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_457_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_504_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_504_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_504_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_504_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
if (lean_obj_tag(v_a_469_) == 0)
{
lean_object* v___x_473_; 
lean_del_object(v___x_471_);
lean_inc_ref(v_e_456_);
v___x_473_ = l_Lean_Meta_Sym_inferType(v_e_456_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_491_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_491_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_491_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_491_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Expr_getAppFn(v_a_474_);
lean_dec(v_a_474_);
if (lean_obj_tag(v___x_478_) == 4)
{
lean_object* v_declName_479_; uint8_t v___x_480_; 
v_declName_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_declName_479_);
lean_dec_ref_known(v___x_478_, 2);
v___x_480_ = l_Lean_NameSet_contains(v_a_469_, v_declName_479_);
lean_dec(v_declName_479_);
lean_dec_ref_known(v_a_469_, 5);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec_ref(v_e_456_);
v___x_481_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_481_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_del_object(v___x_476_);
v___x_485_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_486_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_485_, v_e_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
return v___x_486_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec_ref(v___x_478_);
lean_dec_ref_known(v_a_469_, 5);
lean_dec_ref(v_e_456_);
v___x_487_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_487_);
v___x_489_ = v___x_476_;
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
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec_ref_known(v_a_469_, 5);
lean_dec_ref(v_e_456_);
v_a_492_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_473_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_473_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec_ref(v_e_456_);
v___x_500_ = lean_box(0);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_500_);
v___x_502_ = v___x_471_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v_e_456_);
v_a_505_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_468_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_468_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_456_ = stack[0].m_obj;
lean_object* v_a_457_ = stack[1].m_obj;
lean_object* v_a_458_ = stack[2].m_obj;
lean_object* v_a_459_ = stack[3].m_obj;
lean_object* v_a_460_ = stack[4].m_obj;
lean_object* v_a_461_ = stack[5].m_obj;
lean_object* v_a_462_ = stack[6].m_obj;
lean_object* v_a_463_ = stack[7].m_obj;
lean_object* v_a_464_ = stack[8].m_obj;
lean_object* v_a_465_ = stack[9].m_obj;
lean_object* v_a_466_ = stack[10].m_obj;
lean_object* v_res_513_;
v_res_513_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm___boxed(lean_object* v_e_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec(v_a_515_);
return v_res_526_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(lean_object* v_msgData_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v_env_534_; uint8_t v___x_535_; lean_object* v_env_536_; lean_object* v___x_537_; lean_object* v_toCold_538_; lean_object* v_mctx_539_; lean_object* v_lctx_540_; lean_object* v_options_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_533_ = lean_st_ref_get(v___y_531_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc_ref(v_env_534_);
lean_dec(v___x_533_);
v___x_535_ = 0;
v_env_536_ = l_Lean_Environment_setRecordingDeps(v_env_534_, v___x_535_);
v___x_537_ = lean_st_ref_get(v___y_529_);
v_toCold_538_ = lean_ctor_get(v___y_530_, 0);
v_mctx_539_ = lean_ctor_get(v___x_537_, 0);
lean_inc_ref(v_mctx_539_);
lean_dec(v___x_537_);
v_lctx_540_ = lean_ctor_get(v___y_528_, 2);
v_options_541_ = lean_ctor_get(v_toCold_538_, 2);
lean_inc_ref(v_options_541_);
lean_inc_ref(v_lctx_540_);
v___x_542_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_542_, 0, v_env_536_);
lean_ctor_set(v___x_542_, 1, v_mctx_539_);
lean_ctor_set(v___x_542_, 2, v_lctx_540_);
lean_ctor_set(v___x_542_, 3, v_options_541_);
v___x_543_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_msgData_527_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_527_ = stack[0].m_obj;
lean_object* v___y_528_ = stack[1].m_obj;
lean_object* v___y_529_ = stack[2].m_obj;
lean_object* v___y_530_ = stack[3].m_obj;
lean_object* v___y_531_ = stack[4].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msgData_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0___boxed(lean_object* v_msgData_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msgData_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_553_; double v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_float_of_nat(v___x_553_);
return v___x_554_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(lean_object* v_cls_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_ref_565_; lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_612_; 
v_ref_565_ = lean_ctor_get(v___y_562_, 2);
v___x_566_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_612_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_612_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_612_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v_traceState_572_; lean_object* v_env_573_; lean_object* v_nextMacroScope_574_; lean_object* v_ngen_575_; lean_object* v_auxDeclNGen_576_; lean_object* v_cache_577_; lean_object* v_recordedDeps_578_; lean_object* v_messages_579_; lean_object* v_infoState_580_; lean_object* v_snapshotTasks_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_611_; 
v___x_571_ = lean_st_ref_take(v___y_563_);
v_traceState_572_ = lean_ctor_get(v___x_571_, 4);
v_env_573_ = lean_ctor_get(v___x_571_, 0);
v_nextMacroScope_574_ = lean_ctor_get(v___x_571_, 1);
v_ngen_575_ = lean_ctor_get(v___x_571_, 2);
v_auxDeclNGen_576_ = lean_ctor_get(v___x_571_, 3);
v_cache_577_ = lean_ctor_get(v___x_571_, 5);
v_recordedDeps_578_ = lean_ctor_get(v___x_571_, 6);
v_messages_579_ = lean_ctor_get(v___x_571_, 7);
v_infoState_580_ = lean_ctor_get(v___x_571_, 8);
v_snapshotTasks_581_ = lean_ctor_get(v___x_571_, 9);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_611_ == 0)
{
v___x_583_ = v___x_571_;
v_isShared_584_ = v_isSharedCheck_611_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snapshotTasks_581_);
lean_inc(v_infoState_580_);
lean_inc(v_messages_579_);
lean_inc(v_recordedDeps_578_);
lean_inc(v_cache_577_);
lean_inc(v_traceState_572_);
lean_inc(v_auxDeclNGen_576_);
lean_inc(v_ngen_575_);
lean_inc(v_nextMacroScope_574_);
lean_inc(v_env_573_);
lean_dec(v___x_571_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_611_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint64_t v_tid_585_; lean_object* v_traces_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_610_; 
v_tid_585_ = lean_ctor_get_uint64(v_traceState_572_, sizeof(void*)*1);
v_traces_586_ = lean_ctor_get(v_traceState_572_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_traceState_572_);
if (v_isSharedCheck_610_ == 0)
{
v___x_588_ = v_traceState_572_;
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_traces_586_);
lean_dec(v_traceState_572_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_610_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; double v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_box(0);
v___x_592_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0);
v___x_593_ = 0;
v___x_594_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1));
v___x_595_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_595_, 0, v_cls_558_);
lean_ctor_set(v___x_595_, 1, v___x_591_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
lean_ctor_set_float(v___x_595_, sizeof(void*)*3, v___x_592_);
lean_ctor_set_float(v___x_595_, sizeof(void*)*3 + 8, v___x_592_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3 + 16, v___x_593_);
v___x_596_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2));
v___x_597_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v_a_567_);
lean_ctor_set(v___x_597_, 2, v___x_596_);
lean_inc(v_ref_565_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_ref_565_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_PersistentArray_push___redArg(v_traces_586_, v___x_598_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_599_);
v___x_601_ = v___x_588_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_599_);
lean_ctor_set_uint64(v_reuseFailAlloc_609_, sizeof(void*)*1, v_tid_585_);
v___x_601_ = v_reuseFailAlloc_609_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v___x_601_);
v___x_603_ = v___x_583_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_env_573_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_574_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_575_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_cache_577_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_recordedDeps_578_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_messages_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_infoState_580_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_snapshotTasks_581_);
v___x_603_ = v_reuseFailAlloc_608_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_st_ref_put(v___y_563_, v___x_603_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_590_);
v___x_606_ = v___x_569_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_590_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_558_ = stack[0].m_obj;
lean_object* v_msg_559_ = stack[1].m_obj;
lean_object* v___y_560_ = stack[2].m_obj;
lean_object* v___y_561_ = stack[3].m_obj;
lean_object* v___y_562_ = stack[4].m_obj;
lean_object* v___y_563_ = stack[5].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_558_, v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___boxed(lean_object* v_cls_614_, lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_614_, v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_627_ = l_Lean_Name_append(v___x_626_, v___x_625_);
return v___x_627_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(lean_object* v_generation_628_, lean_object* v_as_629_, size_t v_sz_630_, size_t v_i_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_generation_628_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v_b_632_);
return v___x_645_;
}
else
{
lean_object* v_a_646_; lean_object* v_toCold_647_; lean_object* v_options_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v_inheritedTraceOptions_651_; uint8_t v_hasTrace_652_; lean_object* v___x_653_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; 
v_a_646_ = lean_array_uget_borrowed(v_as_629_, v_i_631_);
v_toCold_647_ = lean_ctor_get(v___y_641_, 0);
v_options_648_ = lean_ctor_get(v_toCold_647_, 2);
v_fst_649_ = lean_ctor_get(v_a_646_, 0);
v_snd_650_ = lean_ctor_get(v_a_646_, 1);
v_inheritedTraceOptions_651_ = lean_ctor_get(v_toCold_647_, 11);
v_hasTrace_652_ = lean_ctor_get_uint8(v_options_648_, sizeof(void*)*1);
v___x_653_ = lean_box(0);
if (v_hasTrace_652_ == 0)
{
v___y_655_ = v___y_633_;
v___y_656_ = v___y_634_;
v___y_657_ = v___y_635_;
v___y_658_ = v___y_636_;
v___y_659_ = v___y_637_;
v___y_660_ = v___y_638_;
v___y_661_ = v___y_639_;
v___y_662_ = v___y_640_;
v___y_663_ = v___y_641_;
v___y_664_ = v___y_642_;
goto v___jp_654_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_672_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2);
v___x_673_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_651_, v_options_648_, v___x_672_);
if (v___x_673_ == 0)
{
v___y_655_ = v___y_633_;
v___y_656_ = v___y_634_;
v___y_657_ = v___y_635_;
v___y_658_ = v___y_636_;
v___y_659_ = v___y_637_;
v___y_660_ = v___y_638_;
v___y_661_ = v___y_639_;
v___y_662_ = v___y_640_;
v___y_663_ = v___y_641_;
v___y_664_ = v___y_642_;
goto v___jp_654_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Meta_Grind_updateLastTag(v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref_known(v___x_674_, 1);
lean_inc(v_snd_650_);
v___x_675_ = l_Lean_MessageData_ofExpr(v_snd_650_);
v___x_676_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_671_, v___x_675_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_dec_ref_known(v___x_676_, 1);
v___y_655_ = v___y_633_;
v___y_656_ = v___y_634_;
v___y_657_ = v___y_635_;
v___y_658_ = v___y_636_;
v___y_659_ = v___y_637_;
v___y_660_ = v___y_638_;
v___y_661_ = v___y_639_;
v___y_662_ = v___y_640_;
v___y_663_ = v___y_641_;
v___y_664_ = v___y_642_;
goto v___jp_654_;
}
else
{
lean_dec(v_generation_628_);
return v___x_676_;
}
}
else
{
lean_dec(v_generation_628_);
return v___x_674_;
}
}
}
v___jp_654_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_box(6);
v___x_666_ = lean_box(1);
lean_inc(v_generation_628_);
lean_inc(v_snd_650_);
lean_inc(v_fst_649_);
v___x_667_ = l_Lean_Meta_Grind_addNewRawFact(v_fst_649_, v_snd_650_, v_generation_628_, v___x_665_, v___x_666_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
size_t v___x_668_; size_t v___x_669_; 
lean_dec_ref_known(v___x_667_, 1);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_631_, v___x_668_);
v_i_631_ = v___x_669_;
v_b_632_ = v___x_653_;
goto _start;
}
else
{
lean_dec(v_generation_628_);
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_generation_628_ = stack[0].m_obj;
lean_object* v_as_629_ = stack[1].m_obj;
size_t v_sz_630_ = stack[2].m_num;
size_t v_i_631_ = stack[3].m_num;
lean_object* v_b_632_ = stack[4].m_obj;
lean_object* v___y_633_ = stack[5].m_obj;
lean_object* v___y_634_ = stack[6].m_obj;
lean_object* v___y_635_ = stack[7].m_obj;
lean_object* v___y_636_ = stack[8].m_obj;
lean_object* v___y_637_ = stack[9].m_obj;
lean_object* v___y_638_ = stack[10].m_obj;
lean_object* v___y_639_ = stack[11].m_obj;
lean_object* v___y_640_ = stack[12].m_obj;
lean_object* v___y_641_ = stack[13].m_obj;
lean_object* v___y_642_ = stack[14].m_obj;
lean_object* v_res_677_;
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_628_, v_as_629_, v_sz_630_, v_i_631_, v_b_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___boxed(lean_object* v_generation_678_, lean_object* v_as_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
size_t v_sz_boxed_694_; size_t v_i_boxed_695_; lean_object* v_res_696_; 
v_sz_boxed_694_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_695_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_678_, v_as_679_, v_sz_boxed_694_, v_i_boxed_695_, v_b_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v_as_679_);
return v_res_696_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(lean_object* v_e_697_, lean_object* v_generation_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Expr_getAppFn(v_e_697_);
if (lean_obj_tag(v___x_710_) == 4)
{
lean_object* v_declName_711_; lean_object* v___x_712_; 
v_declName_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_declName_711_);
lean_dec_ref_known(v___x_710_, 2);
v___x_712_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_699_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_744_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_744_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_744_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_744_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_711_, v_a_713_);
lean_dec(v_a_713_);
lean_dec(v_declName_711_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec(v_generation_698_);
lean_dec_ref(v_e_697_);
v___x_718_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_718_);
v___x_720_ = v___x_715_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v___x_722_; 
lean_del_object(v___x_715_);
v___x_722_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_697_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_box(0);
v_sz_725_ = lean_array_size(v_a_723_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_698_, v_a_723_, v_sz_725_, v___x_726_, v___x_724_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_723_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_727_, 0);
lean_dec(v_unused_735_);
v___x_729_ = v___x_727_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_dec(v___x_727_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_724_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_724_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
return v___x_727_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_generation_698_);
v_a_736_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_722_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_722_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_declName_711_);
lean_dec(v_generation_698_);
lean_dec_ref(v_e_697_);
v_a_745_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_712_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_712_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v___x_710_);
lean_dec(v_generation_698_);
lean_dec_ref(v_e_697_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_697_ = stack[0].m_obj;
lean_object* v_generation_698_ = stack[1].m_obj;
lean_object* v_a_699_ = stack[2].m_obj;
lean_object* v_a_700_ = stack[3].m_obj;
lean_object* v_a_701_ = stack[4].m_obj;
lean_object* v_a_702_ = stack[5].m_obj;
lean_object* v_a_703_ = stack[6].m_obj;
lean_object* v_a_704_ = stack[7].m_obj;
lean_object* v_a_705_ = stack[8].m_obj;
lean_object* v_a_706_ = stack[9].m_obj;
lean_object* v_a_707_ = stack[10].m_obj;
lean_object* v_a_708_ = stack[11].m_obj;
lean_object* v_res_755_;
v_res_755_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_697_, v_generation_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds___boxed(lean_object* v_e_756_, lean_object* v_generation_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_756_, v_generation_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec(v_a_758_);
return v_res_769_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(lean_object* v_cls_770_, lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_770_, v_msg_771_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_783_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_770_ = stack[0].m_obj;
lean_object* v_msg_771_ = stack[1].m_obj;
lean_object* v___y_772_ = stack[2].m_obj;
lean_object* v___y_773_ = stack[3].m_obj;
lean_object* v___y_774_ = stack[4].m_obj;
lean_object* v___y_775_ = stack[5].m_obj;
lean_object* v___y_776_ = stack[6].m_obj;
lean_object* v___y_777_ = stack[7].m_obj;
lean_object* v___y_778_ = stack[8].m_obj;
lean_object* v___y_779_ = stack[9].m_obj;
lean_object* v___y_780_ = stack[10].m_obj;
lean_object* v___y_781_ = stack[11].m_obj;
lean_object* v_res_784_;
v_res_784_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(v_cls_770_, v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___boxed(lean_object* v_cls_785_, lean_object* v_msg_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(v_cls_785_, v_msg_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec(v___y_787_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(lean_object* v_c_799_){
_start:
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_nat_dec_eq(v_c_799_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_sub(v_c_799_, v___x_802_);
v___x_804_ = lean_nat_lxor(v_c_799_, v___x_803_);
lean_dec(v___x_803_);
v___x_805_ = lean_nat_log2(v___x_804_);
lean_dec(v___x_804_);
v___x_806_ = lean_nat_shiftr(v_c_799_, v___x_805_);
v___x_807_ = lean_nat_log2(v___x_806_);
v___x_808_ = lean_nat_add(v___x_807_, v___x_802_);
lean_dec(v___x_807_);
v___x_809_ = lean_nat_add(v___x_806_, v___x_802_);
lean_dec(v___x_806_);
v___x_810_ = lean_nat_shiftl(v___x_802_, v___x_808_);
v___x_811_ = lean_nat_dec_eq(v___x_809_, v___x_810_);
lean_dec(v___x_810_);
lean_dec(v___x_809_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v___x_808_);
lean_dec(v___x_805_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_808_);
lean_ctor_set(v___x_813_, 1, v___x_805_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
else
{
lean_object* v___x_815_; 
v___x_815_ = lean_box(0);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f___boxed(lean_object* v_c_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(v_c_816_);
lean_dec(v_c_816_);
return v_res_817_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = l_Lean_Level_ofNat(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_box(0);
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3);
v___x_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__4);
v___x_829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3);
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__5);
v___x_832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__3);
v___x_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6);
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__2));
v___x_836_ = l_Lean_mkConst(v___x_835_, v___x_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv(lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__7);
v___x_840_ = l_Lean_Nat_mkType;
v___x_841_ = l_Lean_Nat_mkInstHDiv;
v___x_842_ = l_Lean_mkApp6(v___x_839_, v___x_840_, v___x_840_, v___x_840_, v___x_841_, v_a_837_, v_b_838_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv___closed__6);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2));
v___x_850_ = l_Lean_mkConst(v___x_849_, v___x_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(lean_object* v_a_851_, lean_object* v_b_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__3);
v___x_854_ = l_Lean_Nat_mkType;
v___x_855_ = l_Lean_Nat_mkInstHMod;
v___x_856_ = l_Lean_mkApp6(v___x_853_, v___x_854_, v___x_854_, v___x_854_, v___x_855_, v_a_851_, v_b_852_);
return v___x_856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = l_Lean_Level_ofNat(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__3);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__4);
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__2));
v___x_869_ = l_Lean_mkConst(v___x_868_, v___x_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(lean_object* v_a_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl___closed__5);
v___x_872_ = l_Lean_Nat_mkType;
v___x_873_ = l_Lean_mkAppB(v___x_871_, v___x_872_, v_a_870_);
return v___x_873_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(lean_object* v_e_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; uint8_t v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = l_Lean_Expr_cleanupAnnotations(v_e_908_);
v___x_953_ = l_Lean_Expr_isApp(v___x_952_);
if (v___x_953_ == 0)
{
lean_dec_ref(v___x_952_);
goto v___jp_949_;
}
else
{
lean_object* v_arg_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_arg_954_ = lean_ctor_get(v___x_952_, 1);
lean_inc_ref(v_arg_954_);
v___x_955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_952_);
v___x_956_ = l_Lean_Expr_isApp(v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref(v___x_955_);
lean_dec_ref(v_arg_954_);
goto v___jp_949_;
}
else
{
lean_object* v_arg_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_arg_957_ = lean_ctor_get(v___x_955_, 1);
lean_inc_ref(v_arg_957_);
v___x_958_ = l_Lean_Expr_appFnCleanup___redArg(v___x_955_);
v___x_959_ = l_Lean_Expr_isApp(v___x_958_);
if (v___x_959_ == 0)
{
lean_dec_ref(v___x_958_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
goto v___jp_949_;
}
else
{
lean_object* v_arg_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_arg_960_ = lean_ctor_get(v___x_958_, 1);
lean_inc_ref(v_arg_960_);
v___x_961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_958_);
v___x_962_ = l_Lean_Expr_isApp(v___x_961_);
if (v___x_962_ == 0)
{
lean_dec_ref(v___x_961_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
goto v___jp_949_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_961_);
v___x_964_ = l_Lean_Expr_isApp(v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref(v___x_963_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
goto v___jp_949_;
}
else
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_963_);
v___x_966_ = l_Lean_Expr_isApp(v___x_965_);
if (v___x_966_ == 0)
{
lean_dec_ref(v___x_965_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
goto v___jp_949_;
}
else
{
lean_object* v_arg_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_arg_967_ = lean_ctor_get(v___x_965_, 1);
lean_inc_ref(v_arg_967_);
v___x_968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_965_);
v___x_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__3));
v___x_970_ = l_Lean_Expr_isConstOf(v___x_968_, v___x_969_);
lean_dec_ref(v___x_968_);
if (v___x_970_ == 0)
{
lean_dec_ref(v_arg_967_);
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
goto v___jp_949_;
}
else
{
lean_object* v_fst_972_; lean_object* v_fst_973_; lean_object* v_fst_974_; uint8_t v_snd_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13));
v___x_1028_ = l_Lean_Expr_isConstOf(v_arg_967_, v___x_1027_);
lean_dec_ref(v_arg_967_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec_ref(v_arg_960_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
v___x_1029_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1029_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_Structural_isInstHAndNat___redArg(v_arg_960_, v_a_912_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1052_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1052_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1052_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_unbox(v_a_1032_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; uint8_t v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1041_; 
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
v___x_1037_ = lean_alloc_ctor(0, 0, 2);
v___x_1038_ = lean_unbox(v_a_1032_);
lean_ctor_set_uint8(v___x_1037_, 0, v___x_1038_);
v___x_1039_ = lean_unbox(v_a_1032_);
lean_dec(v_a_1032_);
lean_ctor_set_uint8(v___x_1037_, 1, v___x_1039_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1041_ = v___x_1034_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1037_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
else
{
lean_object* v___x_1043_; 
lean_dec(v_a_1032_);
lean_inc_ref(v_arg_954_);
v___x_1043_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_954_);
if (lean_obj_tag(v___x_1043_) == 1)
{
lean_object* v_val_1044_; uint8_t v___x_1045_; 
lean_del_object(v___x_1034_);
v_val_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = 0;
v_fst_972_ = v_arg_957_;
v_fst_973_ = v_arg_954_;
v_fst_974_ = v_val_1044_;
v_snd_975_ = v___x_1045_;
v___y_976_ = v_a_909_;
v___y_977_ = v_a_910_;
v___y_978_ = v_a_911_;
v___y_979_ = v_a_912_;
v___y_980_ = v_a_913_;
v___y_981_ = v_a_914_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1046_; 
lean_dec(v___x_1043_);
lean_inc_ref(v_arg_957_);
v___x_1046_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_957_);
if (lean_obj_tag(v___x_1046_) == 1)
{
lean_object* v_val_1047_; 
lean_del_object(v___x_1034_);
v_val_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_fst_972_ = v_arg_954_;
v_fst_973_ = v_arg_957_;
v_fst_974_ = v_val_1047_;
v_snd_975_ = v___x_970_;
v___y_976_ = v_a_909_;
v___y_977_ = v_a_910_;
v___y_978_ = v_a_911_;
v___y_979_ = v_a_912_;
v___y_980_ = v_a_913_;
v___y_981_ = v_a_914_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_dec(v___x_1046_);
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1048_);
v___x_1050_ = v___x_1034_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_arg_957_);
lean_dec_ref(v_arg_954_);
v_a_1053_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1031_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1031_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
v___jp_971_:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_maskOnesZeros_x3f(v_fst_974_);
lean_dec(v_fst_974_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v_fst_984_ = lean_ctor_get(v_val_983_, 0);
lean_inc_n(v_fst_984_, 2);
v_snd_985_ = lean_ctor_get(v_val_983_, 1);
lean_inc(v_snd_985_);
lean_dec(v_val_983_);
v___x_986_ = l_Lean_mkNatLit(v_fst_984_);
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_nat_shiftl(v___x_987_, v_fst_984_);
lean_dec(v_fst_984_);
v___x_989_ = l_Lean_mkNatLit(v___x_988_);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_nat_dec_eq(v_snd_985_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc(v_snd_985_);
v___x_992_ = l_Lean_mkNatLit(v_snd_985_);
v___x_993_ = lean_nat_shiftl(v___x_987_, v_snd_985_);
lean_dec(v_snd_985_);
v___x_994_ = l_Lean_mkNatLit(v___x_993_);
lean_inc_ref_n(v___x_994_, 2);
lean_inc_ref(v_fst_972_);
v___x_995_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatDiv(v_fst_972_, v___x_994_);
lean_inc_ref(v___x_989_);
v___x_996_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(v___x_995_, v___x_989_);
v___x_997_ = l_Lean_mkNatMul(v___x_996_, v___x_994_);
v___x_998_ = l_Lean_Meta_Sym_shareCommonInc(v___x_997_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_998_) == 0)
{
if (v_snd_975_ == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__6));
v___y_917_ = v_a_999_;
v___y_918_ = v___x_989_;
v___y_919_ = v_fst_973_;
v___y_920_ = v___x_991_;
v___y_921_ = v___x_986_;
v___y_922_ = v_fst_972_;
v___y_923_ = v___x_994_;
v___y_924_ = v___x_992_;
v___y_925_ = v___x_1000_;
goto v___jp_916_;
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__8));
v___y_917_ = v_a_1001_;
v___y_918_ = v___x_989_;
v___y_919_ = v_fst_973_;
v___y_920_ = v___x_991_;
v___y_921_ = v___x_986_;
v___y_922_ = v_fst_972_;
v___y_923_ = v___x_994_;
v___y_924_ = v___x_992_;
v___y_925_ = v___x_1002_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___x_994_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_986_);
lean_dec_ref(v_fst_973_);
lean_dec_ref(v_fst_972_);
v_a_1003_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_998_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_998_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v_snd_985_);
lean_inc_ref(v___x_989_);
lean_inc_ref(v_fst_972_);
v___x_1011_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(v_fst_972_, v___x_989_);
v___x_1012_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1011_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_1012_) == 0)
{
if (v_snd_975_ == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__10));
v___y_935_ = v_a_1013_;
v___y_936_ = v___x_989_;
v___y_937_ = v_fst_973_;
v___y_938_ = v___x_986_;
v___y_939_ = v_fst_972_;
v___y_940_ = v___x_1014_;
goto v___jp_934_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__12));
v___y_935_ = v_a_1015_;
v___y_936_ = v___x_989_;
v___y_937_ = v_fst_973_;
v___y_938_ = v___x_986_;
v___y_939_ = v_fst_972_;
v___y_940_ = v___x_1016_;
goto v___jp_934_;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_986_);
lean_dec_ref(v_fst_973_);
lean_dec_ref(v_fst_972_);
v_a_1017_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1012_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1012_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec(v___x_982_);
lean_dec_ref(v_fst_973_);
lean_dec_ref(v_fst_972_);
v___x_1025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
}
}
}
}
}
}
}
v___jp_916_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_926_ = lean_box(0);
lean_inc(v___y_925_);
v___x_927_ = l_Lean_mkConst(v___y_925_, v___x_926_);
lean_inc_ref(v___y_919_);
v___x_928_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_919_);
lean_inc_ref(v___y_923_);
v___x_929_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_923_);
lean_inc_ref(v___y_918_);
v___x_930_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_918_);
v___x_931_ = l_Lean_mkApp9(v___x_927_, v___y_922_, v___y_919_, v___y_923_, v___y_918_, v___y_924_, v___y_921_, v___x_928_, v___x_929_, v___x_930_);
v___x_932_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_932_, 0, v___y_917_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*2, v___y_920_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*2 + 1, v___y_920_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
v___jp_934_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_941_ = lean_box(0);
lean_inc(v___y_940_);
v___x_942_ = l_Lean_mkConst(v___y_940_, v___x_941_);
lean_inc_ref(v___y_937_);
v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_937_);
lean_inc_ref(v___y_936_);
v___x_944_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v___y_936_);
v___x_945_ = l_Lean_mkApp6(v___x_942_, v___y_939_, v___y_937_, v___y_936_, v___y_938_, v___x_943_, v___x_944_);
v___x_946_ = 0;
v___x_947_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_947_, 0, v___y_935_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*2, v___x_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*2 + 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
v___jp_949_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_908_ = stack[0].m_obj;
lean_object* v_a_909_ = stack[1].m_obj;
lean_object* v_a_910_ = stack[2].m_obj;
lean_object* v_a_911_ = stack[3].m_obj;
lean_object* v_a_912_ = stack[4].m_obj;
lean_object* v_a_913_ = stack[5].m_obj;
lean_object* v_a_914_ = stack[6].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___boxed(lean_object* v_e_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1070_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(lean_object* v_e_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_1071_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1071_ = stack[0].m_obj;
lean_object* v_a_1072_ = stack[1].m_obj;
lean_object* v_a_1073_ = stack[2].m_obj;
lean_object* v_a_1074_ = stack[3].m_obj;
lean_object* v_a_1075_ = stack[4].m_obj;
lean_object* v_a_1076_ = stack[5].m_obj;
lean_object* v_a_1077_ = stack[6].m_obj;
lean_object* v_a_1078_ = stack[7].m_obj;
lean_object* v_a_1079_ = stack[8].m_obj;
lean_object* v_a_1080_ = stack[9].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(v_e_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___boxed(lean_object* v_e_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc(v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
return v_res_1095_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
uint8_t v___y_1128_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = l_Lean_Expr_cleanupAnnotations(v_e_1113_);
v___x_1132_ = l_Lean_Expr_isApp(v___x_1131_);
if (v___x_1132_ == 0)
{
lean_dec_ref(v___x_1131_);
goto v___jp_1121_;
}
else
{
lean_object* v_arg_1133_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_arg_1133_ = lean_ctor_get(v___x_1131_, 1);
lean_inc_ref(v_arg_1133_);
v___x_1147_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1131_);
v___x_1148_ = l_Lean_Expr_isApp(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec_ref(v___x_1147_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1121_;
}
else
{
lean_object* v_arg_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_arg_1149_ = lean_ctor_get(v___x_1147_, 1);
lean_inc_ref(v_arg_1149_);
v___x_1150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1147_);
v___x_1151_ = l_Lean_Expr_isApp(v___x_1150_);
if (v___x_1151_ == 0)
{
lean_dec_ref(v___x_1150_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1121_;
}
else
{
lean_object* v_arg_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_arg_1152_ = lean_ctor_get(v___x_1150_, 1);
lean_inc_ref(v_arg_1152_);
v___x_1153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1150_);
v___x_1154_ = l_Lean_Expr_isApp(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1121_;
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1153_);
v___x_1156_ = l_Lean_Expr_isApp(v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec_ref(v___x_1155_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1121_;
}
else
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1155_);
v___x_1158_ = l_Lean_Expr_isApp(v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec_ref(v___x_1157_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1121_;
}
else
{
lean_object* v_arg_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_arg_1159_ = lean_ctor_get(v___x_1157_, 1);
lean_inc_ref(v_arg_1159_);
v___x_1160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1157_);
v___x_1161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod___closed__2));
v___x_1162_ = l_Lean_Expr_isConstOf(v___x_1160_, v___x_1161_);
lean_dec_ref(v___x_1160_);
if (v___x_1162_ == 0)
{
lean_dec_ref(v_arg_1159_);
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1121_;
}
else
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__13));
v___x_1164_ = l_Lean_Expr_isConstOf(v_arg_1159_, v___x_1163_);
lean_dec_ref(v_arg_1159_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_arg_1152_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
v___x_1165_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1165_, 0, v___x_1164_);
lean_ctor_set_uint8(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_1152_, v_a_1117_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1267_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1267_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1267_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_unbox(v_a_1168_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; uint8_t v___x_1174_; uint8_t v___x_1175_; lean_object* v___x_1177_; 
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
v___x_1173_ = lean_alloc_ctor(0, 0, 2);
v___x_1174_ = lean_unbox(v_a_1168_);
lean_ctor_set_uint8(v___x_1173_, 0, v___x_1174_);
v___x_1175_ = lean_unbox(v_a_1168_);
lean_dec(v_a_1168_);
lean_ctor_set_uint8(v___x_1173_, 1, v___x_1175_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1173_);
v___x_1177_ = v___x_1170_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1173_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
lean_object* v___x_1179_; 
lean_dec(v_a_1168_);
lean_inc_ref(v_arg_1133_);
v___x_1179_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1133_);
if (lean_obj_tag(v___x_1179_) == 1)
{
lean_object* v_val_1180_; lean_object* v_fst_1182_; lean_object* v_fst_1183_; lean_object* v_fst_1184_; uint8_t v_snd_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
lean_del_object(v___x_1170_);
v_val_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_val_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1215_ = l_Lean_Expr_cleanupAnnotations(v_arg_1149_);
v___x_1216_ = l_Lean_Expr_isApp(v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v___x_1215_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v_arg_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_arg_1217_ = lean_ctor_get(v___x_1215_, 1);
lean_inc_ref(v_arg_1217_);
v___x_1218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1215_);
v___x_1219_ = l_Lean_Expr_isApp(v___x_1218_);
if (v___x_1219_ == 0)
{
lean_dec_ref(v___x_1218_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v_arg_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_arg_1220_ = lean_ctor_get(v___x_1218_, 1);
lean_inc_ref(v_arg_1220_);
v___x_1221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1218_);
v___x_1222_ = l_Lean_Expr_isApp(v___x_1221_);
if (v___x_1222_ == 0)
{
lean_dec_ref(v___x_1221_);
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v_arg_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_arg_1223_ = lean_ctor_get(v___x_1221_, 1);
lean_inc_ref(v_arg_1223_);
v___x_1224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1221_);
v___x_1225_ = l_Lean_Expr_isApp(v___x_1224_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v___x_1224_);
lean_dec_ref(v_arg_1223_);
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1224_);
v___x_1227_ = l_Lean_Expr_isApp(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v___x_1226_);
lean_dec_ref(v_arg_1223_);
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1226_);
v___x_1229_ = l_Lean_Expr_isApp(v___x_1228_);
if (v___x_1229_ == 0)
{
lean_dec_ref(v___x_1228_);
lean_dec_ref(v_arg_1223_);
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1228_);
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__6));
v___x_1232_ = l_Lean_Expr_isConstOf(v___x_1230_, v___x_1231_);
lean_dec_ref(v___x_1230_);
if (v___x_1232_ == 0)
{
lean_dec_ref(v_arg_1223_);
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_1223_, v_a_1117_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1254_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1254_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1254_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_unbox(v_a_1234_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; uint8_t v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1243_; 
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
v___x_1239_ = lean_alloc_ctor(0, 0, 2);
v___x_1240_ = lean_unbox(v_a_1234_);
lean_ctor_set_uint8(v___x_1239_, 0, v___x_1240_);
v___x_1241_ = lean_unbox(v_a_1234_);
lean_dec(v_a_1234_);
lean_ctor_set_uint8(v___x_1239_, 1, v___x_1241_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1239_);
v___x_1243_ = v___x_1236_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1239_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_a_1234_);
lean_inc_ref(v_arg_1220_);
v___x_1245_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1220_);
if (lean_obj_tag(v___x_1245_) == 1)
{
lean_object* v_val_1246_; uint8_t v___x_1247_; 
lean_del_object(v___x_1236_);
v_val_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = 0;
v_fst_1182_ = v_arg_1217_;
v_fst_1183_ = v_arg_1220_;
v_fst_1184_ = v_val_1246_;
v_snd_1185_ = v___x_1247_;
v___y_1186_ = v_a_1114_;
v___y_1187_ = v_a_1115_;
v___y_1188_ = v_a_1116_;
v___y_1189_ = v_a_1117_;
v___y_1190_ = v_a_1118_;
v___y_1191_ = v_a_1119_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1248_; 
lean_dec(v___x_1245_);
lean_inc_ref(v_arg_1217_);
v___x_1248_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1217_);
if (lean_obj_tag(v___x_1248_) == 1)
{
lean_object* v_val_1249_; 
lean_del_object(v___x_1236_);
v_val_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v_fst_1182_ = v_arg_1220_;
v_fst_1183_ = v_arg_1217_;
v_fst_1184_ = v_val_1249_;
v_snd_1185_ = v___x_1162_;
v___y_1186_ = v_a_1114_;
v___y_1187_ = v_a_1115_;
v___y_1188_ = v_a_1116_;
v___y_1189_ = v_a_1117_;
v___y_1190_ = v_a_1118_;
v___y_1191_ = v_a_1119_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
lean_dec(v___x_1248_);
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1250_);
v___x_1252_ = v___x_1236_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec_ref(v_arg_1220_);
lean_dec_ref(v_arg_1217_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
v_a_1255_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1233_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1233_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
}
}
}
}
v___jp_1181_:
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_nat_dec_lt(v_fst_1184_, v_val_1180_);
if (v___x_1192_ == 0)
{
lean_dec(v_fst_1184_);
lean_dec_ref(v_fst_1183_);
lean_dec_ref(v_fst_1182_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
v___y_1128_ = v___x_1192_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1193_ = lean_unsigned_to_nat(2u);
v___x_1194_ = lean_nat_mul(v___x_1193_, v_fst_1184_);
v___x_1195_ = lean_nat_dec_lt(v_val_1180_, v___x_1194_);
lean_dec(v___x_1194_);
if (v___x_1195_ == 0)
{
lean_dec(v_fst_1184_);
lean_dec_ref(v_fst_1183_);
lean_dec_ref(v_fst_1182_);
lean_dec(v_val_1180_);
lean_dec_ref(v_arg_1133_);
v___y_1128_ = v___x_1195_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1196_ = lean_nat_sub(v_val_1180_, v_fst_1184_);
lean_dec(v_fst_1184_);
lean_dec(v_val_1180_);
v___x_1197_ = l_Lean_mkNatLit(v___x_1196_);
lean_inc_ref(v_fst_1182_);
lean_inc_ref(v___x_1197_);
v___x_1198_ = l_Lean_mkNatMul(v___x_1197_, v_fst_1182_);
lean_inc_ref_n(v_arg_1133_, 3);
v___x_1199_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(v___x_1198_, v_arg_1133_);
v___x_1200_ = l_Lean_mkNatSub(v_arg_1133_, v___x_1199_);
v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatMod(v___x_1200_, v_arg_1133_);
v___x_1202_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1201_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1202_) == 0)
{
if (v_snd_1185_ == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__1));
v___y_1135_ = v_a_1203_;
v___y_1136_ = v___x_1197_;
v___y_1137_ = v_fst_1183_;
v___y_1138_ = v_fst_1182_;
v___y_1139_ = v___x_1204_;
goto v___jp_1134_;
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1205_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___closed__3));
v___y_1135_ = v_a_1205_;
v___y_1136_ = v___x_1197_;
v___y_1137_ = v_fst_1183_;
v___y_1138_ = v_fst_1182_;
v___y_1139_ = v___x_1206_;
goto v___jp_1134_;
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___x_1197_);
lean_dec_ref(v_fst_1183_);
lean_dec_ref(v_fst_1182_);
lean_dec_ref(v_arg_1133_);
v_a_1207_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1202_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1202_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec(v___x_1179_);
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
v___x_1263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1263_);
v___x_1265_ = v___x_1170_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
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
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_arg_1149_);
lean_dec_ref(v_arg_1133_);
v_a_1268_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1167_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1167_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
}
}
}
}
v___jp_1134_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1140_ = lean_box(0);
lean_inc(v___y_1139_);
v___x_1141_ = l_Lean_mkConst(v___y_1139_, v___x_1140_);
lean_inc_ref(v_arg_1133_);
v___x_1142_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkNatEqRefl(v_arg_1133_);
v___x_1143_ = l_Lean_mkApp5(v___x_1141_, v___y_1138_, v___y_1137_, v___y_1136_, v_arg_1133_, v___x_1142_);
v___x_1144_ = 0;
v___x_1145_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1145_, 0, v___y_1135_);
lean_ctor_set(v___x_1145_, 1, v___x_1143_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*2, v___x_1144_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*2 + 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
v___jp_1121_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg___closed__0));
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1129_, 0, v___y_1128_);
lean_ctor_set_uint8(v___x_1129_, 1, v___y_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1113_ = stack[0].m_obj;
lean_object* v_a_1114_ = stack[1].m_obj;
lean_object* v_a_1115_ = stack[2].m_obj;
lean_object* v_a_1116_ = stack[3].m_obj;
lean_object* v_a_1117_ = stack[4].m_obj;
lean_object* v_a_1118_ = stack[5].m_obj;
lean_object* v_a_1119_ = stack[6].m_obj;
lean_object* v_res_1276_;
v_res_1276_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg(v_e_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
stack->m_obj
 = v_res_1276_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg___boxed(lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg(v_e_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1285_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc(lean_object* v_e_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg(v_e_1286_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1286_ = stack[0].m_obj;
lean_object* v_a_1287_ = stack[1].m_obj;
lean_object* v_a_1288_ = stack[2].m_obj;
lean_object* v_a_1289_ = stack[3].m_obj;
lean_object* v_a_1290_ = stack[4].m_obj;
lean_object* v_a_1291_ = stack[5].m_obj;
lean_object* v_a_1292_ = stack[6].m_obj;
lean_object* v_a_1293_ = stack[7].m_obj;
lean_object* v_a_1294_ = stack[8].m_obj;
lean_object* v_a_1295_ = stack[9].m_obj;
lean_object* v_res_1298_;
v_res_1298_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc(v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___boxed(lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc(v_e_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
return v_res_1310_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1311_, lean_object* v_i_1312_, lean_object* v_k_1313_){
_start:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_array_get_size(v_keys_1311_);
v___x_1315_ = lean_nat_dec_lt(v_i_1312_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec(v_i_1312_);
return v___x_1315_;
}
else
{
lean_object* v_k_x27_1316_; size_t v___x_1317_; size_t v___x_1318_; uint8_t v___x_1319_; 
v_k_x27_1316_ = lean_array_fget_borrowed(v_keys_1311_, v_i_1312_);
v___x_1317_ = lean_ptr_addr(v_k_1313_);
v___x_1318_ = lean_ptr_addr(v_k_x27_1316_);
v___x_1319_ = lean_usize_dec_eq(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_nat_add(v_i_1312_, v___x_1320_);
lean_dec(v_i_1312_);
v_i_1312_ = v___x_1321_;
goto _start;
}
else
{
lean_dec(v_i_1312_);
return v___x_1315_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1311_ = stack[0].m_obj;
lean_object* v_i_1312_ = stack[1].m_obj;
lean_object* v_k_1313_ = stack[2].m_obj;
uint8_t v_res_1323_;
v_res_1323_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_1311_, v_i_1312_, v_k_1313_);
stack->m_num = v_res_1323_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1324_, lean_object* v_i_1325_, lean_object* v_k_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_1324_, v_i_1325_, v_k_1326_);
lean_dec_ref(v_k_1326_);
lean_dec_ref(v_keys_1324_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object* v_x_1329_, size_t v_x_1330_, lean_object* v_x_1331_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
lean_object* v_es_1332_; lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v_j_1336_; lean_object* v___x_1337_; 
v_es_1332_ = lean_ctor_get(v_x_1329_, 0);
v___x_1333_ = lean_box(2);
v___x_1334_ = ((size_t)31ULL);
v___x_1335_ = lean_usize_land(v_x_1330_, v___x_1334_);
v_j_1336_ = lean_usize_to_nat(v___x_1335_);
v___x_1337_ = lean_array_get_borrowed(v___x_1333_, v_es_1332_, v_j_1336_);
lean_dec(v_j_1336_);
switch(lean_obj_tag(v___x_1337_))
{
case 0:
{
lean_object* v_key_1338_; size_t v___x_1339_; size_t v___x_1340_; uint8_t v___x_1341_; 
v_key_1338_ = lean_ctor_get(v___x_1337_, 0);
v___x_1339_ = lean_ptr_addr(v_x_1331_);
v___x_1340_ = lean_ptr_addr(v_key_1338_);
v___x_1341_ = lean_usize_dec_eq(v___x_1339_, v___x_1340_);
return v___x_1341_;
}
case 1:
{
lean_object* v_node_1342_; size_t v___x_1343_; size_t v___x_1344_; 
v_node_1342_ = lean_ctor_get(v___x_1337_, 0);
v___x_1343_ = ((size_t)5ULL);
v___x_1344_ = lean_usize_shift_right(v_x_1330_, v___x_1343_);
v_x_1329_ = v_node_1342_;
v_x_1330_ = v___x_1344_;
goto _start;
}
default: 
{
uint8_t v___x_1346_; 
v___x_1346_ = 0;
return v___x_1346_;
}
}
}
else
{
lean_object* v_ks_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_ks_1347_ = lean_ctor_get(v_x_1329_, 0);
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_ks_1347_, v___x_1348_, v_x_1331_);
return v___x_1349_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1329_ = stack[0].m_obj;
size_t v_x_1330_ = stack[1].m_num;
lean_object* v_x_1331_ = stack[2].m_obj;
uint8_t v_res_1350_;
v_res_1350_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1329_, v_x_1330_, v_x_1331_);
stack->m_num = v_res_1350_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
size_t v_x_10599__boxed_1354_; uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_x_10599__boxed_1354_ = lean_unbox_usize(v_x_1352_);
lean_dec(v_x_1352_);
v_res_1355_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1351_, v_x_10599__boxed_1354_, v_x_1353_);
lean_dec_ref(v_x_1353_);
lean_dec_ref(v_x_1351_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; uint64_t v___x_1362_; size_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1359_ = lean_ptr_addr(v_x_1358_);
v___x_1360_ = ((size_t)3ULL);
v___x_1361_ = lean_usize_shift_right(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_usize_to_uint64(v___x_1361_);
v___x_1363_ = lean_uint64_to_usize(v___x_1362_);
v___x_1364_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1357_, v___x_1363_, v_x_1358_);
return v___x_1364_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1357_ = stack[0].m_obj;
lean_object* v_x_1358_ = stack[1].m_obj;
uint8_t v_res_1365_;
v_res_1365_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_1357_, v_x_1358_);
stack->m_num = v_res_1365_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_1366_, v_x_1367_);
lean_dec_ref(v_x_1367_);
lean_dec_ref(v_x_1366_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object* v_val_1371_, uint8_t v___x_1372_, lean_object* v___x_1373_, lean_object* v_a_1374_, lean_object* v_e_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___y_1387_; lean_object* v_a_1388_; lean_object* v___y_1402_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___x_1410_; 
lean_inc_ref(v_e_1375_);
v___x_1410_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v_e_1375_, v___x_1373_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
if (lean_obj_tag(v_a_1411_) == 0)
{
uint8_t v_done_1412_; uint8_t v_contextDependent_1413_; lean_object* v___y_1415_; lean_object* v_a_1416_; lean_object* v___y_1420_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; 
v_done_1412_ = lean_ctor_get_uint8(v_a_1411_, 0);
v_contextDependent_1413_ = lean_ctor_get_uint8(v_a_1411_, 1);
if (v_done_1412_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref_known(v___x_1410_, 1);
v___x_1428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___closed__0));
lean_inc_ref(v_e_1375_);
v___x_1429_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_1374_, v___x_1428_, v_e_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
if (lean_obj_tag(v_a_1430_) == 0)
{
uint8_t v_done_1431_; uint8_t v_contextDependent_1432_; lean_object* v___y_1434_; lean_object* v_a_1435_; lean_object* v___y_1439_; 
v_done_1431_ = lean_ctor_get_uint8(v_a_1430_, 0);
v_contextDependent_1432_ = lean_ctor_get_uint8(v_a_1430_, 1);
if (v_done_1431_ == 0)
{
lean_object* v___x_1441_; 
lean_dec_ref_known(v___x_1429_, 1);
lean_inc_ref(v_e_1375_);
v___x_1441_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_andMaskSimproc___redArg(v_e_1375_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
if (lean_obj_tag(v_a_1442_) == 0)
{
uint8_t v_done_1443_; 
v_done_1443_ = lean_ctor_get_uint8(v_a_1442_, 0);
if (v_done_1443_ == 0)
{
uint8_t v_contextDependent_1444_; lean_object* v___x_1445_; 
lean_inc_ref(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v_contextDependent_1444_ = lean_ctor_get_uint8(v_a_1442_, 1);
lean_dec_ref_known(v_a_1442_, 0);
lean_inc_ref(v_e_1375_);
v___x_1445_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mulLargeCoeffSimproc___redArg(v_e_1375_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; uint8_t v___y_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
if (v_contextDependent_1444_ == 0)
{
v___y_1439_ = v___x_1445_;
goto v___jp_1438_;
}
else
{
if (lean_obj_tag(v_a_1446_) == 0)
{
uint8_t v_contextDependent_1458_; 
v_contextDependent_1458_ = lean_ctor_get_uint8(v_a_1446_, 1);
v___y_1448_ = v_contextDependent_1458_;
goto v___jp_1447_;
}
else
{
uint8_t v___x_1459_; 
v___x_1459_ = 0;
v___y_1448_ = v___x_1459_;
goto v___jp_1447_;
}
}
v___jp_1447_:
{
if (v___y_1448_ == 0)
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
lean_inc(v_a_1446_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1457_);
v___x_1450_ = v___x_1445_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v___x_1445_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1446_);
lean_inc_ref(v___x_1452_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
v___y_1434_ = v___x_1454_;
v_a_1435_ = v___x_1452_;
goto v___jp_1433_;
}
}
}
else
{
v___y_1439_ = v___x_1445_;
goto v___jp_1438_;
}
}
}
else
{
v___y_1439_ = v___x_1445_;
goto v___jp_1438_;
}
}
else
{
v___y_1439_ = v___x_1441_;
goto v___jp_1438_;
}
}
else
{
v___y_1439_ = v___x_1441_;
goto v___jp_1438_;
}
}
else
{
v___y_1439_ = v___x_1441_;
goto v___jp_1438_;
}
}
else
{
v___y_1420_ = v___x_1429_;
goto v___jp_1419_;
}
v___jp_1433_:
{
if (v_contextDependent_1432_ == 0)
{
v___y_1415_ = v___y_1434_;
v_a_1416_ = v_a_1435_;
goto v___jp_1414_;
}
else
{
if (lean_obj_tag(v_a_1435_) == 0)
{
uint8_t v_contextDependent_1436_; 
v_contextDependent_1436_ = lean_ctor_get_uint8(v_a_1435_, 1);
v___y_1423_ = v___y_1434_;
v___y_1424_ = v_a_1435_;
v___y_1425_ = v_contextDependent_1436_;
goto v___jp_1422_;
}
else
{
uint8_t v_contextDependent_1437_; 
v_contextDependent_1437_ = lean_ctor_get_uint8(v_a_1435_, sizeof(void*)*2 + 1);
v___y_1423_ = v___y_1434_;
v___y_1424_ = v_a_1435_;
v___y_1425_ = v_contextDependent_1437_;
goto v___jp_1422_;
}
}
}
v___jp_1438_:
{
if (lean_obj_tag(v___y_1439_) == 0)
{
lean_object* v_a_1440_; 
v_a_1440_ = lean_ctor_get(v___y_1439_, 0);
lean_inc(v_a_1440_);
v___y_1434_ = v___y_1439_;
v_a_1435_ = v_a_1440_;
goto v___jp_1433_;
}
else
{
lean_dec_ref(v_e_1375_);
return v___y_1439_;
}
}
}
else
{
v___y_1420_ = v___x_1429_;
goto v___jp_1419_;
}
}
else
{
v___y_1420_ = v___x_1429_;
goto v___jp_1419_;
}
}
else
{
v___y_1402_ = v___x_1410_;
goto v___jp_1401_;
}
v___jp_1414_:
{
if (v_contextDependent_1413_ == 0)
{
v___y_1387_ = v___y_1415_;
v_a_1388_ = v_a_1416_;
goto v___jp_1386_;
}
else
{
if (lean_obj_tag(v_a_1416_) == 0)
{
uint8_t v_contextDependent_1417_; 
v_contextDependent_1417_ = lean_ctor_get_uint8(v_a_1416_, 1);
v___y_1405_ = v___y_1415_;
v___y_1406_ = v_a_1416_;
v___y_1407_ = v_contextDependent_1417_;
goto v___jp_1404_;
}
else
{
uint8_t v_contextDependent_1418_; 
v_contextDependent_1418_ = lean_ctor_get_uint8(v_a_1416_, sizeof(void*)*2 + 1);
v___y_1405_ = v___y_1415_;
v___y_1406_ = v_a_1416_;
v___y_1407_ = v_contextDependent_1418_;
goto v___jp_1404_;
}
}
}
v___jp_1419_:
{
if (lean_obj_tag(v___y_1420_) == 0)
{
lean_object* v_a_1421_; 
v_a_1421_ = lean_ctor_get(v___y_1420_, 0);
lean_inc(v_a_1421_);
v___y_1415_ = v___y_1420_;
v_a_1416_ = v_a_1421_;
goto v___jp_1414_;
}
else
{
lean_dec_ref(v_e_1375_);
return v___y_1420_;
}
}
v___jp_1422_:
{
if (v___y_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v___y_1423_);
v___x_1426_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1424_);
lean_inc_ref(v___x_1426_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
v___y_1415_ = v___x_1427_;
v_a_1416_ = v___x_1426_;
goto v___jp_1414_;
}
else
{
v___y_1415_ = v___y_1423_;
v_a_1416_ = v___y_1424_;
goto v___jp_1414_;
}
}
}
else
{
v___y_1402_ = v___x_1410_;
goto v___jp_1401_;
}
}
else
{
v___y_1402_ = v___x_1410_;
goto v___jp_1401_;
}
v___jp_1386_:
{
if (lean_obj_tag(v_a_1388_) == 0)
{
uint8_t v_done_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1400_; 
v_done_1389_ = lean_ctor_get_uint8(v_a_1388_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_a_1388_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1391_ = v_a_1388_;
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v_a_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
if (v_done_1389_ == 0)
{
lean_object* v_toGoalState_1393_; lean_object* v_enodeMap_1394_; uint8_t v___x_1395_; lean_object* v___x_1397_; 
lean_dec_ref(v___y_1387_);
v_toGoalState_1393_ = lean_ctor_get(v_val_1371_, 0);
v_enodeMap_1394_ = lean_ctor_get(v_toGoalState_1393_, 1);
v___x_1395_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_enodeMap_1394_, v_e_1375_);
lean_dec_ref(v_e_1375_);
if (v_isShared_1392_ == 0)
{
v___x_1397_ = v___x_1391_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 0, 2);
v___x_1397_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; 
lean_ctor_set_uint8(v___x_1397_, 0, v___x_1395_);
lean_ctor_set_uint8(v___x_1397_, 1, v___x_1372_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
else
{
lean_del_object(v___x_1391_);
lean_dec_ref(v_e_1375_);
return v___y_1387_;
}
}
}
else
{
lean_dec_ref(v_a_1388_);
lean_dec_ref(v_e_1375_);
return v___y_1387_;
}
}
v___jp_1401_:
{
if (lean_obj_tag(v___y_1402_) == 0)
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_a_1403_);
v___y_1387_ = v___y_1402_;
v_a_1388_ = v_a_1403_;
goto v___jp_1386_;
}
else
{
lean_dec_ref(v_e_1375_);
return v___y_1402_;
}
}
v___jp_1404_:
{
if (v___y_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec_ref(v___y_1405_);
v___x_1408_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1406_);
lean_inc_ref(v___x_1408_);
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
v___y_1387_ = v___x_1409_;
v_a_1388_ = v___x_1408_;
goto v___jp_1386_;
}
else
{
v___y_1387_ = v___y_1405_;
v_a_1388_ = v___y_1406_;
goto v___jp_1386_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1371_ = stack[0].m_obj;
uint8_t v___x_1372_ = stack[1].m_num;
lean_object* v___x_1373_ = stack[2].m_obj;
lean_object* v_a_1374_ = stack[3].m_obj;
lean_object* v_e_1375_ = stack[4].m_obj;
lean_object* v___y_1376_ = stack[5].m_obj;
lean_object* v___y_1377_ = stack[6].m_obj;
lean_object* v___y_1378_ = stack[7].m_obj;
lean_object* v___y_1379_ = stack[8].m_obj;
lean_object* v___y_1380_ = stack[9].m_obj;
lean_object* v___y_1381_ = stack[10].m_obj;
lean_object* v___y_1382_ = stack[11].m_obj;
lean_object* v___y_1383_ = stack[12].m_obj;
lean_object* v___y_1384_ = stack[13].m_obj;
lean_object* v_res_1460_;
v_res_1460_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(v_val_1371_, v___x_1372_, v___x_1373_, v_a_1374_, v_e_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
stack->m_obj
 = v_res_1460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object* v_val_1461_, lean_object* v___x_1462_, lean_object* v___x_1463_, lean_object* v_a_1464_, lean_object* v_e_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v___x_10699__boxed_1476_; lean_object* v_res_1477_; 
v___x_10699__boxed_1476_ = lean_unbox(v___x_1462_);
v_res_1477_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(v_val_1461_, v___x_10699__boxed_1476_, v___x_1463_, v_a_1464_, v_e_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v_a_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v_val_1461_);
return v_res_1477_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_st_ref_get(v_a_1481_);
v___x_1486_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_1481_, v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1498_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1498_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1498_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1496_; 
v___x_1491_ = 0;
v___x_1492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0));
v___x_1493_ = lean_box(v___x_1491_);
v___f_1494_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed), 15, 4);
lean_closure_set(v___f_1494_, 0, v___x_1485_);
lean_closure_set(v___f_1494_, 1, v___x_1493_);
lean_closure_set(v___f_1494_, 2, v___x_1492_);
lean_closure_set(v___f_1494_, 3, v_a_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___f_1494_);
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___f_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v___x_1485_);
v_a_1499_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1486_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1486_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1481_ = stack[0].m_obj;
lean_object* v_a_1482_ = stack[1].m_obj;
lean_object* v_a_1483_ = stack[2].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1481_, v_a_1482_, v_a_1483_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___boxed(lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
return v_res_1512_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1513_, v_a_1521_, v_a_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1513_ = stack[0].m_obj;
lean_object* v_a_1514_ = stack[1].m_obj;
lean_object* v_a_1515_ = stack[2].m_obj;
lean_object* v_a_1516_ = stack[3].m_obj;
lean_object* v_a_1517_ = stack[4].m_obj;
lean_object* v_a_1518_ = stack[5].m_obj;
lean_object* v_a_1519_ = stack[6].m_obj;
lean_object* v_a_1520_ = stack[7].m_obj;
lean_object* v_a_1521_ = stack[8].m_obj;
lean_object* v_a_1522_ = stack[9].m_obj;
lean_object* v_res_1525_;
v_res_1525_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
stack->m_obj
 = v_res_1525_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___boxed(lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec(v_a_1526_);
return v_res_1537_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_object* v_00_u03b2_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_1539_, v_x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1539_ = stack[1].m_obj;
lean_object* v_x_1540_ = stack[2].m_obj;
uint8_t v_res_1542_;
v_res_1542_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_box(0), v_x_1539_, v_x_1540_);
stack->m_num = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___boxed(lean_object* v_00_u03b2_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_){
_start:
{
uint8_t v_res_1546_; lean_object* v_r_1547_; 
v_res_1546_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(v_00_u03b2_1543_, v_x_1544_, v_x_1545_);
lean_dec_ref(v_x_1545_);
lean_dec_ref(v_x_1544_);
v_r_1547_ = lean_box(v_res_1546_);
return v_r_1547_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_object* v_00_u03b2_1548_, lean_object* v_x_1549_, size_t v_x_1550_, lean_object* v_x_1551_){
_start:
{
uint8_t v___x_1552_; 
v___x_1552_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_1549_, v_x_1550_, v_x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1549_ = stack[1].m_obj;
size_t v_x_1550_ = stack[2].m_num;
lean_object* v_x_1551_ = stack[3].m_obj;
uint8_t v_res_1553_;
v_res_1553_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_box(0), v_x_1549_, v_x_1550_, v_x_1551_);
stack->m_num = v_res_1553_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
size_t v_x_11123__boxed_1558_; uint8_t v_res_1559_; lean_object* v_r_1560_; 
v_x_11123__boxed_1558_ = lean_unbox_usize(v_x_1556_);
lean_dec(v_x_1556_);
v_res_1559_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(v_00_u03b2_1554_, v_x_1555_, v_x_11123__boxed_1558_, v_x_1557_);
lean_dec_ref(v_x_1557_);
lean_dec_ref(v_x_1555_);
v_r_1560_ = lean_box(v_res_1559_);
return v_r_1560_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1561_, lean_object* v_keys_1562_, lean_object* v_vals_1563_, lean_object* v_heq_1564_, lean_object* v_i_1565_, lean_object* v_k_1566_){
_start:
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_1562_, v_i_1565_, v_k_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1562_ = stack[1].m_obj;
lean_object* v_vals_1563_ = stack[2].m_obj;
lean_object* v_i_1565_ = stack[4].m_obj;
lean_object* v_k_1566_ = stack[5].m_obj;
uint8_t v_res_1568_;
v_res_1568_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_box(0), v_keys_1562_, v_vals_1563_, lean_box(0), v_i_1565_, v_k_1566_);
stack->m_num = v_res_1568_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1569_, lean_object* v_keys_1570_, lean_object* v_vals_1571_, lean_object* v_heq_1572_, lean_object* v_i_1573_, lean_object* v_k_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(v_00_u03b2_1569_, v_keys_1570_, v_vals_1571_, v_heq_1572_, v_i_1573_, v_k_1574_);
lean_dec_ref(v_k_1574_);
lean_dec_ref(v_vals_1571_);
lean_dec_ref(v_keys_1570_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0(lean_object* v_s_1577_){
_start:
{
lean_object* v_internalized_1578_; uint8_t v_initialized_1579_; lean_object* v_thms_1580_; lean_object* v_preds_1581_; lean_object* v_sourceTypes_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_internalized_1578_ = lean_ctor_get(v_s_1577_, 1);
v_initialized_1579_ = lean_ctor_get_uint8(v_s_1577_, sizeof(void*)*5);
v_thms_1580_ = lean_ctor_get(v_s_1577_, 2);
v_preds_1581_ = lean_ctor_get(v_s_1577_, 3);
v_sourceTypes_1582_ = lean_ctor_get(v_s_1577_, 4);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_s_1577_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v_s_1577_, 0);
lean_dec(v_unused_1591_);
v___x_1584_ = v_s_1577_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_sourceTypes_1582_);
lean_inc(v_preds_1581_);
lean_inc(v_thms_1580_);
lean_inc(v_internalized_1578_);
lean_dec(v_s_1577_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_internalized_1578_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_thms_1580_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_preds_1581_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_sourceTypes_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*5, v_initialized_1579_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(lean_object* v_snd_1592_, lean_object* v_s_1593_){
_start:
{
lean_object* v_persistentCache_1594_; lean_object* v_internalized_1595_; uint8_t v_initialized_1596_; lean_object* v_thms_1597_; lean_object* v_preds_1598_; lean_object* v_sourceTypes_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_persistentCache_1594_ = lean_ctor_get(v_snd_1592_, 1);
v_internalized_1595_ = lean_ctor_get(v_s_1593_, 1);
v_initialized_1596_ = lean_ctor_get_uint8(v_s_1593_, sizeof(void*)*5);
v_thms_1597_ = lean_ctor_get(v_s_1593_, 2);
v_preds_1598_ = lean_ctor_get(v_s_1593_, 3);
v_sourceTypes_1599_ = lean_ctor_get(v_s_1593_, 4);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_s_1593_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_s_1593_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v_s_1593_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_sourceTypes_1599_);
lean_inc(v_preds_1598_);
lean_inc(v_thms_1597_);
lean_inc(v_internalized_1595_);
lean_dec(v_s_1593_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
lean_inc_ref(v_persistentCache_1594_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_persistentCache_1594_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_persistentCache_1594_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_internalized_1595_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_thms_1597_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_preds_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_sourceTypes_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*5, v_initialized_1596_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed(lean_object* v_snd_1608_, lean_object* v_s_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(v_snd_1608_, v_s_1609_);
lean_dec_ref(v_snd_1608_);
return v_res_1610_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(lean_object* v_e_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___f_1624_; lean_object* v___x_1625_; 
v___f_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0));
v___x_1625_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1616_, v_a_1621_, v_a_1622_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_n(v_a_1626_, 2);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1626_);
lean_ctor_set(v___x_1627_, 1, v_a_1626_);
v___x_1628_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1629_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1628_, v_a_1616_, v_a_1621_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v_cache_1631_; lean_object* v___x_1632_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v_cache_1631_ = lean_ctor_get(v_a_1630_, 0);
lean_inc_ref(v_cache_1631_);
lean_dec(v_a_1630_);
v___x_1632_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1628_, v___f_1624_, v_a_1616_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1632_, 1);
v___x_1633_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1633_, 0, v_e_1615_);
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1));
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_1637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v_cache_1631_);
lean_ctor_set(v___x_1637_, 2, v___x_1636_);
lean_ctor_set(v___x_1637_, 3, v___x_1636_);
v___x_1638_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1633_, v___x_1627_, v___x_1634_, v___x_1637_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v_fst_1640_; lean_object* v_snd_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1673_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v_fst_1640_ = lean_ctor_get(v_a_1639_, 0);
v_snd_1641_ = lean_ctor_get(v_a_1639_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1639_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1643_ = v_a_1639_;
v_isShared_1644_ = v_isSharedCheck_1673_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snd_1641_);
lean_inc(v_fst_1640_);
lean_dec(v_a_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1673_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; 
v___f_1645_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1645_, 0, v_snd_1641_);
v___x_1646_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1628_, v___f_1645_, v_a_1616_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1663_; 
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v___x_1646_, 0);
lean_dec(v_unused_1664_);
v___x_1648_ = v___x_1646_;
v_isShared_1649_ = v_isSharedCheck_1663_;
goto v_resetjp_1647_;
}
else
{
lean_dec(v___x_1646_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1663_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
if (lean_obj_tag(v_fst_1640_) == 1)
{
lean_object* v_e_x27_1650_; lean_object* v_proof_1651_; lean_object* v___x_1653_; 
v_e_x27_1650_ = lean_ctor_get(v_fst_1640_, 0);
lean_inc_ref(v_e_x27_1650_);
v_proof_1651_ = lean_ctor_get(v_fst_1640_, 1);
lean_inc_ref(v_proof_1651_);
lean_dec_ref_known(v_fst_1640_, 2);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v_proof_1651_);
lean_ctor_set(v___x_1643_, 0, v_e_x27_1650_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_e_x27_1650_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_proof_1651_);
v___x_1653_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1654_);
v___x_1656_ = v___x_1648_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_del_object(v___x_1643_);
lean_dec(v_fst_1640_);
v___x_1659_ = lean_box(0);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 0, v___x_1659_);
v___x_1661_ = v___x_1648_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_del_object(v___x_1643_);
lean_dec(v_fst_1640_);
v_a_1665_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1646_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1646_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1638_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1638_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v_cache_1631_);
lean_dec_ref_known(v___x_1627_, 2);
lean_dec_ref(v_e_1615_);
v_a_1682_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1632_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1632_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec_ref_known(v___x_1627_, 2);
lean_dec_ref(v_e_1615_);
v_a_1690_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1629_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1629_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_e_1615_);
v_a_1698_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1625_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1625_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1615_ = stack[0].m_obj;
lean_object* v_a_1616_ = stack[1].m_obj;
lean_object* v_a_1617_ = stack[2].m_obj;
lean_object* v_a_1618_ = stack[3].m_obj;
lean_object* v_a_1619_ = stack[4].m_obj;
lean_object* v_a_1620_ = stack[5].m_obj;
lean_object* v_a_1621_ = stack[6].m_obj;
lean_object* v_a_1622_ = stack[7].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___boxed(lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
return v_res_1716_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(lean_object* v_e_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1717_, v_a_1718_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1717_ = stack[0].m_obj;
lean_object* v_a_1718_ = stack[1].m_obj;
lean_object* v_a_1719_ = stack[2].m_obj;
lean_object* v_a_1720_ = stack[3].m_obj;
lean_object* v_a_1721_ = stack[4].m_obj;
lean_object* v_a_1722_ = stack[5].m_obj;
lean_object* v_a_1723_ = stack[6].m_obj;
lean_object* v_a_1724_ = stack[7].m_obj;
lean_object* v_a_1725_ = stack[8].m_obj;
lean_object* v_a_1726_ = stack[9].m_obj;
lean_object* v_a_1727_ = stack[10].m_obj;
lean_object* v_res_1730_;
v_res_1730_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(v_e_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
stack->m_obj
 = v_res_1730_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___boxed(lean_object* v_e_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(v_e_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec(v_a_1732_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v_ks_1748_; lean_object* v_vs_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1775_; 
v_ks_1748_ = lean_ctor_get(v_x_1744_, 0);
v_vs_1749_ = lean_ctor_get(v_x_1744_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_x_1744_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1751_ = v_x_1744_;
v_isShared_1752_ = v_isSharedCheck_1775_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_vs_1749_);
lean_inc(v_ks_1748_);
lean_dec(v_x_1744_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1775_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_ks_1748_);
v___x_1754_ = lean_nat_dec_lt(v_x_1745_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec(v_x_1745_);
v___x_1755_ = lean_array_push(v_ks_1748_, v_x_1746_);
v___x_1756_ = lean_array_push(v_vs_1749_, v_x_1747_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1756_);
lean_ctor_set(v___x_1751_, 0, v___x_1755_);
v___x_1758_ = v___x_1751_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
else
{
lean_object* v_k_x27_1760_; size_t v___x_1761_; size_t v___x_1762_; uint8_t v___x_1763_; 
v_k_x27_1760_ = lean_array_fget_borrowed(v_ks_1748_, v_x_1745_);
v___x_1761_ = lean_ptr_addr(v_x_1746_);
v___x_1762_ = lean_ptr_addr(v_k_x27_1760_);
v___x_1763_ = lean_usize_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1765_; 
if (v_isShared_1752_ == 0)
{
v___x_1765_ = v___x_1751_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_ks_1748_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_vs_1749_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_nat_add(v_x_1745_, v___x_1766_);
lean_dec(v_x_1745_);
v_x_1744_ = v___x_1765_;
v_x_1745_ = v___x_1767_;
goto _start;
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1770_ = lean_array_fset(v_ks_1748_, v_x_1745_, v_x_1746_);
v___x_1771_ = lean_array_fset(v_vs_1749_, v_x_1745_, v_x_1747_);
lean_dec(v_x_1745_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1771_);
lean_ctor_set(v___x_1751_, 0, v___x_1770_);
v___x_1773_ = v___x_1751_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1776_, lean_object* v_k_1777_, lean_object* v_v_1778_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1776_, v___x_1779_, v_k_1777_, v_v_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1781_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(lean_object* v_x_1782_, size_t v_x_1783_, size_t v_x_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v_es_1787_; size_t v___x_1788_; size_t v___x_1789_; lean_object* v_j_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_es_1787_ = lean_ctor_get(v_x_1782_, 0);
v___x_1788_ = ((size_t)31ULL);
v___x_1789_ = lean_usize_land(v_x_1783_, v___x_1788_);
v_j_1790_ = lean_usize_to_nat(v___x_1789_);
v___x_1791_ = lean_array_get_size(v_es_1787_);
v___x_1792_ = lean_nat_dec_lt(v_j_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_dec(v_j_1790_);
lean_dec(v_x_1786_);
lean_dec_ref(v_x_1785_);
return v_x_1782_;
}
else
{
lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1833_; 
lean_inc_ref(v_es_1787_);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_x_1782_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v_x_1782_, 0);
lean_dec(v_unused_1834_);
v___x_1794_ = v_x_1782_;
v_isShared_1795_ = v_isSharedCheck_1833_;
goto v_resetjp_1793_;
}
else
{
lean_dec(v_x_1782_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1833_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_v_1796_; lean_object* v___x_1797_; lean_object* v_xs_x27_1798_; lean_object* v___y_1800_; 
v_v_1796_ = lean_array_fget(v_es_1787_, v_j_1790_);
v___x_1797_ = lean_box(0);
v_xs_x27_1798_ = lean_array_fset(v_es_1787_, v_j_1790_, v___x_1797_);
switch(lean_obj_tag(v_v_1796_))
{
case 0:
{
lean_object* v_key_1805_; lean_object* v_val_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1818_; 
v_key_1805_ = lean_ctor_get(v_v_1796_, 0);
v_val_1806_ = lean_ctor_get(v_v_1796_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_v_1796_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1808_ = v_v_1796_;
v_isShared_1809_ = v_isSharedCheck_1818_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_val_1806_);
lean_inc(v_key_1805_);
lean_dec(v_v_1796_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1818_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
size_t v___x_1810_; size_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = lean_ptr_addr(v_x_1785_);
v___x_1811_ = lean_ptr_addr(v_key_1805_);
v___x_1812_ = lean_usize_dec_eq(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_del_object(v___x_1808_);
v___x_1813_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1805_, v_val_1806_, v_x_1785_, v_x_1786_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
v___y_1800_ = v___x_1814_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1816_; 
lean_dec(v_val_1806_);
lean_dec(v_key_1805_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v_x_1786_);
lean_ctor_set(v___x_1808_, 0, v_x_1785_);
v___x_1816_ = v___x_1808_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_x_1785_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_x_1786_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
v___y_1800_ = v___x_1816_;
goto v___jp_1799_;
}
}
}
}
case 1:
{
lean_object* v_node_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1831_; 
v_node_1819_ = lean_ctor_get(v_v_1796_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_v_1796_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1821_ = v_v_1796_;
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_node_1819_);
lean_dec(v_v_1796_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
size_t v___x_1823_; size_t v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1823_ = ((size_t)5ULL);
v___x_1824_ = lean_usize_shift_right(v_x_1783_, v___x_1823_);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_x_1784_, v___x_1825_);
v___x_1827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_node_1819_, v___x_1824_, v___x_1826_, v_x_1785_, v_x_1786_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1827_);
v___x_1829_ = v___x_1821_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
v___y_1800_ = v___x_1829_;
goto v___jp_1799_;
}
}
}
default: 
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v_x_1785_);
lean_ctor_set(v___x_1832_, 1, v_x_1786_);
v___y_1800_ = v___x_1832_;
goto v___jp_1799_;
}
}
v___jp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = lean_array_fset(v_xs_x27_1798_, v_j_1790_, v___y_1800_);
lean_dec(v_j_1790_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1801_);
v___x_1803_ = v___x_1794_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_object* v_ks_1835_; lean_object* v_vs_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1854_; 
v_ks_1835_ = lean_ctor_get(v_x_1782_, 0);
v_vs_1836_ = lean_ctor_get(v_x_1782_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_x_1782_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1838_ = v_x_1782_;
v_isShared_1839_ = v_isSharedCheck_1854_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_vs_1836_);
lean_inc(v_ks_1835_);
lean_dec(v_x_1782_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1854_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_ks_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_vs_1836_);
v___x_1841_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v_newNode_1842_; size_t v___x_1843_; uint8_t v___x_1844_; 
v_newNode_1842_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v___x_1841_, v_x_1785_, v_x_1786_);
v___x_1843_ = ((size_t)7ULL);
v___x_1844_ = lean_usize_dec_le(v___x_1843_, v_x_1784_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1842_);
v___x_1846_ = lean_unsigned_to_nat(4u);
v___x_1847_ = lean_nat_dec_lt(v___x_1845_, v___x_1846_);
lean_dec(v___x_1845_);
if (v___x_1847_ == 0)
{
lean_object* v_ks_1848_; lean_object* v_vs_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_ks_1848_ = lean_ctor_get(v_newNode_1842_, 0);
lean_inc_ref(v_ks_1848_);
v_vs_1849_ = lean_ctor_get(v_newNode_1842_, 1);
lean_inc_ref(v_vs_1849_);
lean_dec_ref(v_newNode_1842_);
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0);
v___x_1852_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_x_1784_, v_ks_1848_, v_vs_1849_, v___x_1850_, v___x_1851_);
lean_dec_ref(v_vs_1849_);
lean_dec_ref(v_ks_1848_);
return v___x_1852_;
}
else
{
return v_newNode_1842_;
}
}
else
{
return v_newNode_1842_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1782_ = stack[0].m_obj;
size_t v_x_1783_ = stack[1].m_num;
size_t v_x_1784_ = stack[2].m_num;
lean_object* v_x_1785_ = stack[3].m_obj;
lean_object* v_x_1786_ = stack[4].m_obj;
lean_object* v_res_1855_;
v_res_1855_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1782_, v_x_1783_, v_x_1784_, v_x_1785_, v_x_1786_);
stack->m_obj
 = v_res_1855_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_1856_, lean_object* v_keys_1857_, lean_object* v_vals_1858_, lean_object* v_i_1859_, lean_object* v_entries_1860_){
_start:
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_array_get_size(v_keys_1857_);
v___x_1862_ = lean_nat_dec_lt(v_i_1859_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec(v_i_1859_);
return v_entries_1860_;
}
else
{
lean_object* v_k_1863_; lean_object* v_v_1864_; size_t v___x_1865_; size_t v___x_1866_; size_t v___x_1867_; uint64_t v___x_1868_; size_t v_h_1869_; size_t v___x_1870_; lean_object* v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; size_t v_h_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_k_1863_ = lean_array_fget_borrowed(v_keys_1857_, v_i_1859_);
v_v_1864_ = lean_array_fget_borrowed(v_vals_1858_, v_i_1859_);
v___x_1865_ = lean_ptr_addr(v_k_1863_);
v___x_1866_ = ((size_t)3ULL);
v___x_1867_ = lean_usize_shift_right(v___x_1865_, v___x_1866_);
v___x_1868_ = lean_usize_to_uint64(v___x_1867_);
v_h_1869_ = lean_uint64_to_usize(v___x_1868_);
v___x_1870_ = ((size_t)5ULL);
v___x_1871_ = lean_unsigned_to_nat(1u);
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_sub(v_depth_1856_, v___x_1872_);
v___x_1874_ = lean_usize_mul(v___x_1870_, v___x_1873_);
v_h_1875_ = lean_usize_shift_right(v_h_1869_, v___x_1874_);
v___x_1876_ = lean_nat_add(v_i_1859_, v___x_1871_);
lean_dec(v_i_1859_);
lean_inc(v_v_1864_);
lean_inc(v_k_1863_);
v___x_1877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_entries_1860_, v_h_1875_, v_depth_1856_, v_k_1863_, v_v_1864_);
v_i_1859_ = v___x_1876_;
v_entries_1860_ = v___x_1877_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1856_ = stack[0].m_num;
lean_object* v_keys_1857_ = stack[1].m_obj;
lean_object* v_vals_1858_ = stack[2].m_obj;
lean_object* v_i_1859_ = stack[3].m_obj;
lean_object* v_entries_1860_ = stack[4].m_obj;
lean_object* v_res_1879_;
v_res_1879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_1856_, v_keys_1857_, v_vals_1858_, v_i_1859_, v_entries_1860_);
stack->m_obj
 = v_res_1879_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1880_, lean_object* v_keys_1881_, lean_object* v_vals_1882_, lean_object* v_i_1883_, lean_object* v_entries_1884_){
_start:
{
size_t v_depth_boxed_1885_; lean_object* v_res_1886_; 
v_depth_boxed_1885_ = lean_unbox_usize(v_depth_1880_);
lean_dec(v_depth_1880_);
v_res_1886_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1885_, v_keys_1881_, v_vals_1882_, v_i_1883_, v_entries_1884_);
lean_dec_ref(v_vals_1882_);
lean_dec_ref(v_keys_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
size_t v_x_28838__boxed_1892_; size_t v_x_28839__boxed_1893_; lean_object* v_res_1894_; 
v_x_28838__boxed_1892_ = lean_unbox_usize(v_x_1888_);
lean_dec(v_x_1888_);
v_x_28839__boxed_1893_ = lean_unbox_usize(v_x_1889_);
lean_dec(v_x_1889_);
v_res_1894_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1887_, v_x_28838__boxed_1892_, v_x_28839__boxed_1893_, v_x_1890_, v_x_1891_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; uint64_t v___x_1901_; size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1898_ = lean_ptr_addr(v_x_1896_);
v___x_1899_ = ((size_t)3ULL);
v___x_1900_ = lean_usize_shift_right(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_usize_to_uint64(v___x_1900_);
v___x_1902_ = lean_uint64_to_usize(v___x_1901_);
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1895_, v___x_1902_, v___x_1903_, v_x_1896_, v_x_1897_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0(lean_object* v_e_1905_, lean_object* v_s_1906_){
_start:
{
lean_object* v_cache_1907_; lean_object* v_internalized_1908_; uint8_t v_initialized_1909_; lean_object* v_thms_1910_; lean_object* v_preds_1911_; lean_object* v_sourceTypes_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1921_; 
v_cache_1907_ = lean_ctor_get(v_s_1906_, 0);
v_internalized_1908_ = lean_ctor_get(v_s_1906_, 1);
v_initialized_1909_ = lean_ctor_get_uint8(v_s_1906_, sizeof(void*)*5);
v_thms_1910_ = lean_ctor_get(v_s_1906_, 2);
v_preds_1911_ = lean_ctor_get(v_s_1906_, 3);
v_sourceTypes_1912_ = lean_ctor_get(v_s_1906_, 4);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_s_1906_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1914_ = v_s_1906_;
v_isShared_1915_ = v_isSharedCheck_1921_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_sourceTypes_1912_);
lean_inc(v_preds_1911_);
lean_inc(v_thms_1910_);
lean_inc(v_internalized_1908_);
lean_inc(v_cache_1907_);
lean_dec(v_s_1906_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1921_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_internalized_1908_, v_e_1905_, v___x_1916_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___x_1917_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_cache_1907_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_thms_1910_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_preds_1911_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_sourceTypes_1912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*5, v_initialized_1909_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_1926_ = l_Lean_Name_append(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg(lean_object* v_e_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v___f_1942_; lean_object* v___x_1943_; 
lean_inc_ref(v_e_1930_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1942_, 0, v_e_1930_);
v___x_1943_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1933_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2062_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_2062_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2062_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
uint8_t v_hom_1948_; 
v_hom_1948_ = lean_ctor_get_uint8(v_a_1944_, sizeof(void*)*14 + 24);
lean_dec(v_a_1944_);
if (v_hom_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec_ref(v___f_1942_);
lean_dec_ref(v_e_1930_);
v___x_1949_ = lean_box(0);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1949_);
v___x_1951_ = v___x_1946_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
else
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
v___x_1953_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0));
v___x_1954_ = l_Lean_Expr_isAppOf(v_e_1930_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_del_object(v___x_1946_);
v___x_1955_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1956_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1955_, v_a_1931_, v_a_1939_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2049_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_2049_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2049_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_internalized_1961_; uint8_t v___x_1962_; 
v_internalized_1961_ = lean_ctor_get(v_a_1957_, 1);
lean_inc_ref(v_internalized_1961_);
lean_dec(v_a_1957_);
v___x_1962_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_internalized_1961_, v_e_1930_);
lean_dec_ref(v_internalized_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_del_object(v___x_1959_);
v___x_1963_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1955_, v___f_1942_, v_a_1931_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref_known(v___x_1963_, 1);
lean_inc_ref(v_e_1930_);
v___x_1964_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref_known(v___x_1964_, 1);
v___x_1965_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1930_, v_a_1931_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
lean_inc_ref(v_e_1930_);
v___x_1967_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1930_, v_a_1931_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
if (lean_obj_tag(v_a_1968_) == 1)
{
lean_object* v_val_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2027_; 
v_val_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_a_1968_, 1);
v_fst_1970_ = lean_ctor_get(v_val_1969_, 0);
v_snd_1971_ = lean_ctor_get(v_val_1969_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_val_1969_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1973_ = v_val_1969_;
v_isShared_1974_ = v_isSharedCheck_2027_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snd_1971_);
lean_inc(v_fst_1970_);
lean_dec(v_val_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2027_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; 
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc(v_a_1931_);
v___x_1975_ = lean_grind_preprocess(v_fst_1970_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_n(v_a_1976_, 2);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1977_ = l_Lean_Meta_Simp_Result_getProof(v_a_1976_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = l_Lean_Meta_mkEqTrans(v_snd_1971_, v_a_1978_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v_expr_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_expr_1981_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref_n(v_expr_1981_, 2);
lean_dec(v_a_1976_);
v___x_1982_ = lean_box(0);
lean_inc(v_a_1940_);
lean_inc_ref(v_a_1939_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc(v_a_1931_);
v___x_1983_ = lean_grind_internalize(v_expr_1981_, v_a_1966_, v___x_1982_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_toCold_1984_; lean_object* v_options_1985_; uint8_t v_hasTrace_1986_; 
lean_dec_ref_known(v___x_1983_, 1);
v_toCold_1984_ = lean_ctor_get(v_a_1939_, 0);
v_options_1985_ = lean_ctor_get(v_toCold_1984_, 2);
v_hasTrace_1986_ = lean_ctor_get_uint8(v_options_1985_, sizeof(void*)*1);
if (v_hasTrace_1986_ == 0)
{
lean_object* v___x_1987_; 
lean_del_object(v___x_1973_);
v___x_1987_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1930_, v_expr_1981_, v_a_1980_, v___x_1962_, v_a_1931_, v_a_1933_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1987_;
}
else
{
lean_object* v_inheritedTraceOptions_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_inheritedTraceOptions_1988_ = lean_ctor_get(v_toCold_1984_, 11);
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1990_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1);
v___x_1991_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1988_, v_options_1985_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_del_object(v___x_1973_);
v___x_1992_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1930_, v_expr_1981_, v_a_1980_, v___x_1962_, v_a_1931_, v_a_1933_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Meta_Grind_updateLastTag(v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
lean_dec_ref_known(v___x_1993_, 1);
lean_inc_ref(v_e_1930_);
v___x_1994_ = l_Lean_MessageData_ofExpr(v_e_1930_);
v___x_1995_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 7);
lean_ctor_set(v___x_1973_, 1, v___x_1995_);
lean_ctor_set(v___x_1973_, 0, v___x_1994_);
v___x_1997_ = v___x_1973_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_inc_ref(v_expr_1981_);
v___x_1998_ = l_Lean_MessageData_ofExpr(v_expr_1981_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1989_, v___x_1999_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2001_; 
lean_dec_ref_known(v___x_2000_, 1);
v___x_2001_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1930_, v_expr_1981_, v_a_1980_, v___x_1962_, v_a_1931_, v_a_1933_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_2001_;
}
else
{
lean_dec_ref(v_expr_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_e_1930_);
return v___x_2000_;
}
}
}
else
{
lean_dec_ref(v_expr_1981_);
lean_dec(v_a_1980_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_e_1930_);
return v___x_1993_;
}
}
}
}
else
{
lean_dec_ref(v_expr_1981_);
lean_dec(v_a_1980_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_e_1930_);
return v___x_1983_;
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v_a_1976_);
lean_del_object(v___x_1973_);
lean_dec(v_a_1966_);
lean_dec_ref(v_e_1930_);
v_a_2003_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1979_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1979_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1976_);
lean_del_object(v___x_1973_);
lean_dec(v_snd_1971_);
lean_dec(v_a_1966_);
lean_dec_ref(v_e_1930_);
v_a_2011_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1977_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1977_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_del_object(v___x_1973_);
lean_dec(v_snd_1971_);
lean_dec(v_a_1966_);
lean_dec_ref(v_e_1930_);
v_a_2019_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1975_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1975_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
lean_object* v___x_2028_; 
lean_dec(v_a_1968_);
v___x_2028_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_1930_, v_a_1966_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_1966_);
lean_dec_ref(v_e_1930_);
v_a_2029_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1967_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1967_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_e_1930_);
v_a_2037_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1965_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1965_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_dec_ref(v_e_1930_);
return v___x_1964_;
}
}
else
{
lean_dec_ref(v_e_1930_);
return v___x_1963_;
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec_ref(v___f_1942_);
lean_dec_ref(v_e_1930_);
v___x_2045_ = lean_box(0);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_2045_);
v___x_2047_ = v___x_1959_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v___f_1942_);
lean_dec_ref(v_e_1930_);
v_a_2050_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1956_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1956_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec_ref(v___f_1942_);
lean_dec_ref(v_e_1930_);
v___x_2058_ = lean_box(0);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_2058_);
v___x_2060_ = v___x_1946_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
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
lean_dec_ref(v___f_1942_);
lean_dec_ref(v_e_1930_);
v_a_2063_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_1943_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_1943_);
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
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Homo_internalize___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1930_ = stack[0].m_obj;
lean_object* v_a_1931_ = stack[1].m_obj;
lean_object* v_a_1932_ = stack[2].m_obj;
lean_object* v_a_1933_ = stack[3].m_obj;
lean_object* v_a_1934_ = stack[4].m_obj;
lean_object* v_a_1935_ = stack[5].m_obj;
lean_object* v_a_1936_ = stack[6].m_obj;
lean_object* v_a_1937_ = stack[7].m_obj;
lean_object* v_a_1938_ = stack[8].m_obj;
lean_object* v_a_1939_ = stack[9].m_obj;
lean_object* v_a_1940_ = stack[10].m_obj;
lean_object* v_res_2071_;
v_res_2071_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
stack->m_obj
 = v_res_2071_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___boxed(lean_object* v_e_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec(v_a_2073_);
return v_res_2084_;
}
}
lean_object* l_Lean_Meta_Grind_Homo_internalize(lean_object* v_e_2085_, lean_object* v___parent_x3f_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_2085_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Homo_internalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2085_ = stack[0].m_obj;
lean_object* v___parent_x3f_2086_ = stack[1].m_obj;
lean_object* v_a_2087_ = stack[2].m_obj;
lean_object* v_a_2088_ = stack[3].m_obj;
lean_object* v_a_2089_ = stack[4].m_obj;
lean_object* v_a_2090_ = stack[5].m_obj;
lean_object* v_a_2091_ = stack[6].m_obj;
lean_object* v_a_2092_ = stack[7].m_obj;
lean_object* v_a_2093_ = stack[8].m_obj;
lean_object* v_a_2094_ = stack[9].m_obj;
lean_object* v_a_2095_ = stack[10].m_obj;
lean_object* v_a_2096_ = stack[11].m_obj;
lean_object* v_res_2099_;
v_res_2099_ = l_Lean_Meta_Grind_Homo_internalize(v_e_2085_, v___parent_x3f_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
stack->m_obj
 = v_res_2099_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___boxed(lean_object* v_e_2100_, lean_object* v___parent_x3f_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Meta_Grind_Homo_internalize(v_e_2100_, v___parent_x3f_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec(v___parent_x3f_2101_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0(lean_object* v_00_u03b2_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_x_2115_, v_x_2116_, v_x_2117_);
return v___x_2118_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_object* v_00_u03b2_2119_, lean_object* v_x_2120_, size_t v_x_2121_, size_t v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_2120_, v_x_2121_, v_x_2122_, v_x_2123_, v_x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2120_ = stack[1].m_obj;
size_t v_x_2121_ = stack[2].m_num;
size_t v_x_2122_ = stack[3].m_num;
lean_object* v_x_2123_ = stack[4].m_obj;
lean_object* v_x_2124_ = stack[5].m_obj;
lean_object* v_res_2126_;
v_res_2126_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_box(0), v_x_2120_, v_x_2121_, v_x_2122_, v_x_2123_, v_x_2124_);
stack->m_obj
 = v_res_2126_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2127_, lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
size_t v_x_29584__boxed_2133_; size_t v_x_29585__boxed_2134_; lean_object* v_res_2135_; 
v_x_29584__boxed_2133_ = lean_unbox_usize(v_x_2129_);
lean_dec(v_x_2129_);
v_x_29585__boxed_2134_ = lean_unbox_usize(v_x_2130_);
lean_dec(v_x_2130_);
v_res_2135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(v_00_u03b2_2127_, v_x_2128_, v_x_29584__boxed_2133_, v_x_29585__boxed_2134_, v_x_2131_, v_x_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2136_, lean_object* v_n_2137_, lean_object* v_k_2138_, lean_object* v_v_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v_n_2137_, v_k_2138_, v_v_2139_);
return v___x_2140_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2141_, size_t v_depth_2142_, lean_object* v_keys_2143_, lean_object* v_vals_2144_, lean_object* v_heq_2145_, lean_object* v_i_2146_, lean_object* v_entries_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_2142_, v_keys_2143_, v_vals_2144_, v_i_2146_, v_entries_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2142_ = stack[1].m_num;
lean_object* v_keys_2143_ = stack[2].m_obj;
lean_object* v_vals_2144_ = stack[3].m_obj;
lean_object* v_i_2146_ = stack[5].m_obj;
lean_object* v_entries_2147_ = stack[6].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_box(0), v_depth_2142_, v_keys_2143_, v_vals_2144_, lean_box(0), v_i_2146_, v_entries_2147_);
stack->m_obj
 = v_res_2149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2150_, lean_object* v_depth_2151_, lean_object* v_keys_2152_, lean_object* v_vals_2153_, lean_object* v_heq_2154_, lean_object* v_i_2155_, lean_object* v_entries_2156_){
_start:
{
size_t v_depth_boxed_2157_; lean_object* v_res_2158_; 
v_depth_boxed_2157_ = lean_unbox_usize(v_depth_2151_);
lean_dec(v_depth_2151_);
v_res_2158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(v_00_u03b2_2150_, v_depth_boxed_2157_, v_keys_2152_, v_vals_2153_, v_heq_2154_, v_i_2155_, v_entries_2156_);
lean_dec_ref(v_vals_2153_);
lean_dec_ref(v_keys_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2160_, v_x_2161_, v_x_2162_, v_x_2163_);
return v___x_2164_;
}
}
lean_object* l_Lean_Meta_Grind_Homo_processNewEq(lean_object* v_a_2165_, lean_object* v_b_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2169_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2326_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2326_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2326_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
uint8_t v_hom_2183_; 
v_hom_2183_ = lean_ctor_get_uint8(v_a_2179_, sizeof(void*)*14 + 24);
lean_dec(v_a_2179_);
if (v_hom_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v___x_2184_ = lean_box(0);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2188_; 
lean_del_object(v___x_2181_);
lean_inc_ref(v_b_2166_);
lean_inc_ref(v_a_2165_);
v___x_2188_ = l_Lean_Meta_Grind_hasSameType(v_a_2165_, v_b_2166_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2317_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2317_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2317_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
uint8_t v___x_2193_; 
v___x_2193_ = lean_unbox(v_a_2189_);
lean_dec(v_a_2189_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v___x_2194_ = lean_box(0);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2194_);
v___x_2196_ = v___x_2191_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
lean_object* v___x_2198_; 
lean_del_object(v___x_2191_);
lean_inc_ref(v_b_2166_);
lean_inc_ref(v_a_2165_);
v___x_2198_ = l_Lean_Meta_mkEq(v_a_2165_, v_b_2166_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = l_Lean_Meta_Sym_shareCommon(v_a_2199_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2202_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc_n(v_a_2201_, 2);
lean_dec_ref_known(v___x_2200_, 1);
v___x_2202_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_2201_, v_a_2167_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2292_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2292_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2292_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
if (lean_obj_tag(v_a_2203_) == 1)
{
lean_object* v_val_2207_; lean_object* v_fst_2208_; lean_object* v_snd_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2287_; 
lean_del_object(v___x_2205_);
v_val_2207_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v_a_2203_, 1);
v_fst_2208_ = lean_ctor_get(v_val_2207_, 0);
v_snd_2209_ = lean_ctor_get(v_val_2207_, 1);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_val_2207_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2211_ = v_val_2207_;
v_isShared_2212_ = v_isSharedCheck_2287_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_snd_2209_);
lean_inc(v_fst_2208_);
lean_dec(v_val_2207_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2287_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; 
lean_inc(v_a_2176_);
lean_inc_ref(v_a_2175_);
lean_inc(v_a_2174_);
lean_inc_ref(v_a_2173_);
lean_inc(v_a_2172_);
lean_inc_ref(v_a_2171_);
lean_inc(v_a_2170_);
lean_inc_ref(v_a_2169_);
lean_inc(v_a_2168_);
lean_inc(v_a_2167_);
lean_inc_ref(v_b_2166_);
lean_inc_ref(v_a_2165_);
v___x_2213_ = lean_grind_mk_eq_proof(v_a_2165_, v_b_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
lean_inc(v_fst_2208_);
lean_inc(v_a_2201_);
v___x_2215_ = l_Lean_Meta_mkEqMPCore(v_a_2201_, v_fst_2208_, v_snd_2209_, v_a_2214_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___x_2232_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2232_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2165_, v_a_2167_);
lean_dec_ref(v_a_2165_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2234_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_2166_, v_a_2167_);
lean_dec_ref(v_b_2166_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___y_2237_; uint8_t v___x_2254_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2254_ = lean_nat_dec_le(v_a_2233_, v_a_2235_);
if (v___x_2254_ == 0)
{
lean_dec(v_a_2235_);
v___y_2237_ = v_a_2233_;
goto v___jp_2236_;
}
else
{
lean_dec(v_a_2233_);
v___y_2237_ = v_a_2235_;
goto v___jp_2236_;
}
v___jp_2236_:
{
lean_object* v_toCold_2238_; lean_object* v_options_2239_; uint8_t v_hasTrace_2240_; 
v_toCold_2238_ = lean_ctor_get(v_a_2175_, 0);
v_options_2239_ = lean_ctor_get(v_toCold_2238_, 2);
v_hasTrace_2240_ = lean_ctor_get_uint8(v_options_2239_, sizeof(void*)*1);
if (v_hasTrace_2240_ == 0)
{
lean_del_object(v___x_2211_);
lean_dec(v_a_2201_);
v___y_2218_ = v___y_2237_;
v___y_2219_ = v_a_2167_;
v___y_2220_ = v_a_2168_;
v___y_2221_ = v_a_2169_;
v___y_2222_ = v_a_2170_;
v___y_2223_ = v_a_2171_;
v___y_2224_ = v_a_2172_;
v___y_2225_ = v_a_2173_;
v___y_2226_ = v_a_2174_;
v___y_2227_ = v_a_2175_;
v___y_2228_ = v_a_2176_;
goto v___jp_2217_;
}
else
{
lean_object* v_inheritedTraceOptions_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_inheritedTraceOptions_2241_ = lean_ctor_get(v_toCold_2238_, 11);
v___x_2242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_2243_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1);
v___x_2244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2241_, v_options_2239_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_del_object(v___x_2211_);
lean_dec(v_a_2201_);
v___y_2218_ = v___y_2237_;
v___y_2219_ = v_a_2167_;
v___y_2220_ = v_a_2168_;
v___y_2221_ = v_a_2169_;
v___y_2222_ = v_a_2170_;
v___y_2223_ = v_a_2171_;
v___y_2224_ = v_a_2172_;
v___y_2225_ = v_a_2173_;
v___y_2226_ = v_a_2174_;
v___y_2227_ = v_a_2175_;
v___y_2228_ = v_a_2176_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Meta_Grind_updateLastTag(v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
lean_dec_ref_known(v___x_2245_, 1);
v___x_2246_ = l_Lean_MessageData_ofExpr(v_a_2201_);
v___x_2247_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3);
if (v_isShared_2212_ == 0)
{
lean_ctor_set_tag(v___x_2211_, 7);
lean_ctor_set(v___x_2211_, 1, v___x_2247_);
lean_ctor_set(v___x_2211_, 0, v___x_2246_);
v___x_2249_ = v___x_2211_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_inc(v_fst_2208_);
v___x_2250_ = l_Lean_MessageData_ofExpr(v_fst_2208_);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_2242_, v___x_2251_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_dec_ref_known(v___x_2252_, 1);
v___y_2218_ = v___y_2237_;
v___y_2219_ = v_a_2167_;
v___y_2220_ = v_a_2168_;
v___y_2221_ = v_a_2169_;
v___y_2222_ = v_a_2170_;
v___y_2223_ = v_a_2171_;
v___y_2224_ = v_a_2172_;
v___y_2225_ = v_a_2173_;
v___y_2226_ = v_a_2174_;
v___y_2227_ = v_a_2175_;
v___y_2228_ = v_a_2176_;
goto v___jp_2217_;
}
else
{
lean_dec(v___y_2237_);
lean_dec(v_a_2216_);
lean_dec(v_fst_2208_);
return v___x_2252_;
}
}
}
else
{
lean_dec(v___y_2237_);
lean_dec(v_a_2216_);
lean_del_object(v___x_2211_);
lean_dec(v_fst_2208_);
lean_dec(v_a_2201_);
return v___x_2245_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2233_);
lean_dec(v_a_2216_);
lean_del_object(v___x_2211_);
lean_dec(v_fst_2208_);
lean_dec(v_a_2201_);
v_a_2255_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2234_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2234_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2216_);
lean_del_object(v___x_2211_);
lean_dec(v_fst_2208_);
lean_dec(v_a_2201_);
lean_dec_ref(v_b_2166_);
v_a_2263_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2232_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2232_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
v___jp_2217_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_box(6);
v___x_2230_ = lean_box(1);
v___x_2231_ = l_Lean_Meta_Grind_addNewRawFact(v_a_2216_, v_fst_2208_, v___y_2218_, v___x_2229_, v___x_2230_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2231_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_del_object(v___x_2211_);
lean_dec(v_fst_2208_);
lean_dec(v_a_2201_);
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2271_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2215_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2215_);
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
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_del_object(v___x_2211_);
lean_dec(v_snd_2209_);
lean_dec(v_fst_2208_);
lean_dec(v_a_2201_);
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2279_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2213_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2213_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_dec(v_a_2203_);
lean_dec(v_a_2201_);
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v___x_2288_ = lean_box(0);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2288_);
v___x_2290_ = v___x_2205_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_a_2201_);
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2293_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2202_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2202_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2301_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2200_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2200_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2309_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2198_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2198_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2318_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2188_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2188_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v_b_2166_);
lean_dec_ref(v_a_2165_);
v_a_2327_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2178_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2178_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Homo_processNewEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2165_ = stack[0].m_obj;
lean_object* v_b_2166_ = stack[1].m_obj;
lean_object* v_a_2167_ = stack[2].m_obj;
lean_object* v_a_2168_ = stack[3].m_obj;
lean_object* v_a_2169_ = stack[4].m_obj;
lean_object* v_a_2170_ = stack[5].m_obj;
lean_object* v_a_2171_ = stack[6].m_obj;
lean_object* v_a_2172_ = stack[7].m_obj;
lean_object* v_a_2173_ = stack[8].m_obj;
lean_object* v_a_2174_ = stack[9].m_obj;
lean_object* v_a_2175_ = stack[10].m_obj;
lean_object* v_a_2176_ = stack[11].m_obj;
lean_object* v_res_2335_;
v_res_2335_ = l_Lean_Meta_Grind_Homo_processNewEq(v_a_2165_, v_b_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
stack->m_obj
 = v_res_2335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq___boxed(lean_object* v_a_2336_, lean_object* v_b_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_Grind_Homo_processNewEq(v_a_2336_, v_b_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec(v_a_2338_);
return v_res_2349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_box(0);
v___x_2354_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1));
v___x_2355_ = l_Lean_mkConst(v___x_2354_, v___x_2353_);
return v___x_2355_;
}
}
lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq(lean_object* v_a_2356_, lean_object* v_b_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2360_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2530_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2530_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2530_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
uint8_t v_hom_2374_; 
v_hom_2374_ = lean_ctor_get_uint8(v_a_2370_, sizeof(void*)*14 + 24);
lean_dec(v_a_2370_);
if (v_hom_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v___x_2375_ = lean_box(0);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2375_);
v___x_2377_ = v___x_2372_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
else
{
lean_object* v___x_2379_; 
lean_del_object(v___x_2372_);
lean_inc_ref(v_b_2357_);
lean_inc_ref(v_a_2356_);
v___x_2379_ = l_Lean_Meta_Grind_hasSameType(v_a_2356_, v_b_2357_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2521_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2521_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2521_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_unbox(v_a_2380_);
lean_dec(v_a_2380_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v___x_2385_ = lean_box(0);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2385_);
v___x_2387_ = v___x_2382_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
else
{
lean_object* v___x_2389_; 
lean_del_object(v___x_2382_);
lean_inc_ref(v_b_2357_);
lean_inc_ref(v_a_2356_);
v___x_2389_ = l_Lean_Meta_mkEq(v_a_2356_, v_b_2357_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = l_Lean_Meta_Sym_shareCommon(v_a_2390_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_n(v_a_2392_, 2);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_2392_, v_a_2358_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2496_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2496_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2496_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
if (lean_obj_tag(v_a_2394_) == 1)
{
lean_object* v_val_2398_; lean_object* v_fst_2399_; lean_object* v_snd_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2491_; 
lean_del_object(v___x_2396_);
v_val_2398_ = lean_ctor_get(v_a_2394_, 0);
lean_inc(v_val_2398_);
lean_dec_ref_known(v_a_2394_, 1);
v_fst_2399_ = lean_ctor_get(v_val_2398_, 0);
v_snd_2400_ = lean_ctor_get(v_val_2398_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_val_2398_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2402_ = v_val_2398_;
v_isShared_2403_ = v_isSharedCheck_2491_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snd_2400_);
lean_inc(v_fst_2399_);
lean_dec(v_val_2398_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2491_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; 
lean_inc_ref(v_b_2357_);
lean_inc_ref(v_a_2356_);
v___x_2404_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_2356_, v_b_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2, &l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2_once, _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2);
v___x_2407_ = l_Lean_Meta_mkCongrArg(v___x_2406_, v_snd_2400_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Lean_mkNot(v_a_2392_);
v___x_2410_ = l_Lean_mkNot(v_fst_2399_);
lean_inc_ref(v___x_2410_);
lean_inc_ref(v___x_2409_);
v___x_2411_ = l_Lean_Meta_mkEqMPCore(v___x_2409_, v___x_2410_, v_a_2408_, v_a_2405_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___x_2428_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2428_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_2356_, v_a_2358_);
lean_dec_ref(v_a_2356_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_2357_, v_a_2358_);
lean_dec_ref(v_b_2357_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___y_2433_; uint8_t v___x_2450_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2450_ = lean_nat_dec_le(v_a_2429_, v_a_2431_);
if (v___x_2450_ == 0)
{
lean_dec(v_a_2431_);
v___y_2433_ = v_a_2429_;
goto v___jp_2432_;
}
else
{
lean_dec(v_a_2429_);
v___y_2433_ = v_a_2431_;
goto v___jp_2432_;
}
v___jp_2432_:
{
lean_object* v_toCold_2434_; lean_object* v_options_2435_; uint8_t v_hasTrace_2436_; 
v_toCold_2434_ = lean_ctor_get(v_a_2366_, 0);
v_options_2435_ = lean_ctor_get(v_toCold_2434_, 2);
v_hasTrace_2436_ = lean_ctor_get_uint8(v_options_2435_, sizeof(void*)*1);
if (v_hasTrace_2436_ == 0)
{
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2402_);
v___y_2414_ = v___y_2433_;
v___y_2415_ = v_a_2358_;
v___y_2416_ = v_a_2359_;
v___y_2417_ = v_a_2360_;
v___y_2418_ = v_a_2361_;
v___y_2419_ = v_a_2362_;
v___y_2420_ = v_a_2363_;
v___y_2421_ = v_a_2364_;
v___y_2422_ = v_a_2365_;
v___y_2423_ = v_a_2366_;
v___y_2424_ = v_a_2367_;
goto v___jp_2413_;
}
else
{
lean_object* v_inheritedTraceOptions_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_inheritedTraceOptions_2437_ = lean_ctor_get(v_toCold_2434_, 11);
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_2439_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1);
v___x_2440_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2437_, v_options_2435_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2402_);
v___y_2414_ = v___y_2433_;
v___y_2415_ = v_a_2358_;
v___y_2416_ = v_a_2359_;
v___y_2417_ = v_a_2360_;
v___y_2418_ = v_a_2361_;
v___y_2419_ = v_a_2362_;
v___y_2420_ = v_a_2363_;
v___y_2421_ = v_a_2364_;
v___y_2422_ = v_a_2365_;
v___y_2423_ = v_a_2366_;
v___y_2424_ = v_a_2367_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Meta_Grind_updateLastTag(v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
lean_dec_ref_known(v___x_2441_, 1);
v___x_2442_ = l_Lean_MessageData_ofExpr(v___x_2409_);
v___x_2443_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3);
if (v_isShared_2403_ == 0)
{
lean_ctor_set_tag(v___x_2402_, 7);
lean_ctor_set(v___x_2402_, 1, v___x_2443_);
lean_ctor_set(v___x_2402_, 0, v___x_2442_);
v___x_2445_ = v___x_2402_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_inc_ref(v___x_2410_);
v___x_2446_ = l_Lean_MessageData_ofExpr(v___x_2410_);
v___x_2447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_2438_, v___x_2447_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_dec_ref_known(v___x_2448_, 1);
v___y_2414_ = v___y_2433_;
v___y_2415_ = v_a_2358_;
v___y_2416_ = v_a_2359_;
v___y_2417_ = v_a_2360_;
v___y_2418_ = v_a_2361_;
v___y_2419_ = v_a_2362_;
v___y_2420_ = v_a_2363_;
v___y_2421_ = v_a_2364_;
v___y_2422_ = v_a_2365_;
v___y_2423_ = v_a_2366_;
v___y_2424_ = v_a_2367_;
goto v___jp_2413_;
}
else
{
lean_dec(v___y_2433_);
lean_dec(v_a_2412_);
lean_dec_ref(v___x_2410_);
return v___x_2448_;
}
}
}
else
{
lean_dec(v___y_2433_);
lean_dec(v_a_2412_);
lean_dec_ref(v___x_2410_);
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2402_);
return v___x_2441_;
}
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_a_2429_);
lean_dec(v_a_2412_);
lean_dec_ref(v___x_2410_);
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2402_);
v_a_2451_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2430_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2430_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_a_2412_);
lean_dec_ref(v___x_2410_);
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2402_);
lean_dec_ref(v_b_2357_);
v_a_2459_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2428_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2428_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
v___jp_2413_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_box(6);
v___x_2426_ = lean_box(1);
v___x_2427_ = l_Lean_Meta_Grind_addNewRawFact(v_a_2412_, v___x_2410_, v___y_2414_, v___x_2425_, v___x_2426_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2427_;
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v___x_2410_);
lean_dec_ref(v___x_2409_);
lean_del_object(v___x_2402_);
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2467_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2411_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2411_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_a_2405_);
lean_del_object(v___x_2402_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2392_);
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2475_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2407_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2407_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_del_object(v___x_2402_);
lean_dec(v_snd_2400_);
lean_dec(v_fst_2399_);
lean_dec(v_a_2392_);
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2483_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2404_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2404_);
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
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_dec(v_a_2394_);
lean_dec(v_a_2392_);
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v___x_2492_ = lean_box(0);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2492_);
v___x_2494_ = v___x_2396_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2497_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2393_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2393_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2505_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2391_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2391_);
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
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2513_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2389_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2389_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2522_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2379_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2379_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_b_2357_);
lean_dec_ref(v_a_2356_);
v_a_2531_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2369_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2369_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Homo_processNewDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2356_ = stack[0].m_obj;
lean_object* v_b_2357_ = stack[1].m_obj;
lean_object* v_a_2358_ = stack[2].m_obj;
lean_object* v_a_2359_ = stack[3].m_obj;
lean_object* v_a_2360_ = stack[4].m_obj;
lean_object* v_a_2361_ = stack[5].m_obj;
lean_object* v_a_2362_ = stack[6].m_obj;
lean_object* v_a_2363_ = stack[7].m_obj;
lean_object* v_a_2364_ = stack[8].m_obj;
lean_object* v_a_2365_ = stack[9].m_obj;
lean_object* v_a_2366_ = stack[10].m_obj;
lean_object* v_a_2367_ = stack[11].m_obj;
lean_object* v_res_2539_;
v_res_2539_ = l_Lean_Meta_Grind_Homo_processNewDiseq(v_a_2356_, v_b_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
stack->m_obj
 = v_res_2539_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___boxed(lean_object* v_a_2540_, lean_object* v_b_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_Grind_Homo_processNewDiseq(v_a_2540_, v_b_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec(v_a_2542_);
return v_res_2553_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_apply_11(v___y_2555_, v___y_2554_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, lean_box(0));
return v___x_2567_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2554_ = stack[0].m_obj;
lean_object* v___y_2555_ = stack[1].m_obj;
lean_object* v___y_2556_ = stack[2].m_obj;
lean_object* v___y_2557_ = stack[3].m_obj;
lean_object* v___y_2558_ = stack[4].m_obj;
lean_object* v___y_2559_ = stack[5].m_obj;
lean_object* v___y_2560_ = stack[6].m_obj;
lean_object* v___y_2561_ = stack[7].m_obj;
lean_object* v___y_2562_ = stack[8].m_obj;
lean_object* v___y_2563_ = stack[9].m_obj;
lean_object* v___y_2564_ = stack[10].m_obj;
lean_object* v___y_2565_ = stack[11].m_obj;
lean_object* v_res_2568_;
v_res_2568_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
stack->m_obj
 = v_res_2568_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref(v___y_2571_);
return v_res_2582_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(uint8_t v___x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_box(v___x_2583_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2583_ = stack[0].m_num;
lean_object* v___y_2584_ = stack[1].m_obj;
lean_object* v___y_2585_ = stack[2].m_obj;
lean_object* v___y_2586_ = stack[3].m_obj;
lean_object* v___y_2587_ = stack[4].m_obj;
lean_object* v___y_2588_ = stack[5].m_obj;
lean_object* v___y_2589_ = stack[6].m_obj;
lean_object* v___y_2590_ = stack[7].m_obj;
lean_object* v___y_2591_ = stack[8].m_obj;
lean_object* v___y_2592_ = stack[9].m_obj;
lean_object* v___y_2593_ = stack[10].m_obj;
lean_object* v_res_2597_;
v_res_2597_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
stack->m_obj
 = v_res_2597_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
uint8_t v___x_1055__boxed_2610_; lean_object* v_res_2611_; 
v___x_1055__boxed_2610_ = lean_unbox(v___x_2598_);
v_res_2611_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_1055__boxed_2610_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec(v___y_2599_);
return v_res_2611_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2612_);
return v___x_2624_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2612_ = stack[0].m_obj;
lean_object* v___y_2613_ = stack[1].m_obj;
lean_object* v___y_2614_ = stack[2].m_obj;
lean_object* v___y_2615_ = stack[3].m_obj;
lean_object* v___y_2616_ = stack[4].m_obj;
lean_object* v___y_2617_ = stack[5].m_obj;
lean_object* v___y_2618_ = stack[6].m_obj;
lean_object* v___y_2619_ = stack[7].m_obj;
lean_object* v___y_2620_ = stack[8].m_obj;
lean_object* v___y_2621_ = stack[9].m_obj;
lean_object* v___y_2622_ = stack[10].m_obj;
lean_object* v_res_2625_;
v_res_2625_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
stack->m_obj
 = v_res_2625_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
return v_res_2638_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v___f_2655_; lean_object* v___x_2656_; 
v___f_2649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2650_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2656_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_2650_, v___x_2651_, v___x_2652_, v___x_2653_, v___f_2654_, v___f_2649_, v___f_2654_, v___f_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2657_;
v_res_2657_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
return v_res_2659_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Extra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_Homo_homExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_Homo_homExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Extra(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
}
#ifdef __cplusplus
}
#endif
