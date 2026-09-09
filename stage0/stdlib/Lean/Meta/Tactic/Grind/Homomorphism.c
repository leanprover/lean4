// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Homomorphism
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Homo public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Tactic.Grind.Diseq import Lean.Meta.Sym.Simp.Rewrite
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\n===>\n"};
static const lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_();
return v_res_89_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_unsigned_to_nat(2531264644u);
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_97_ = l_Lean_Name_num___override(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_100_ = l_Lean_Name_str___override(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_103_ = l_Lean_Name_str___override(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_106_ = l_Lean_Name_num___override(v___x_105_, v___x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_109_ = 1;
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_);
v___x_111_ = l_Lean_registerTraceClass(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_();
return v_res_113_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_114_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__0);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0___closed__1);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(lean_object* v___x_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v___x_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(v___x_122_);
return v_res_124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_129_ = l_Lean_NameSet_empty;
v___x_130_ = lean_box(1);
v___x_131_ = 0;
v___x_132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_134_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v___x_130_);
lean_ctor_set(v___x_134_, 4, v___x_129_);
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*5, v___x_131_);
return v___x_134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_135_; lean_object* v___f_136_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___f_136_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_136_, 0, v___x_135_);
return v___f_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_138_; lean_object* v___x_139_; 
v___f_138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_139_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2____boxed(lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_();
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(uint8_t v___x_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_s_146_){
_start:
{
lean_object* v_cache_147_; lean_object* v_internalized_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_cache_147_ = lean_ctor_get(v_s_146_, 0);
v_internalized_148_ = lean_ctor_get(v_s_146_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_s_146_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_156_ = lean_ctor_get(v_s_146_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_s_146_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_s_146_, 2);
lean_dec(v_unused_158_);
v___x_150_ = v_s_146_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_internalized_148_);
lean_inc(v_cache_147_);
lean_dec(v_s_146_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v_a_145_);
lean_ctor_set(v___x_150_, 3, v_a_144_);
lean_ctor_set(v___x_150_, 2, v_a_143_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_cache_147_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_internalized_148_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_a_143_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_a_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_a_145_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*5, v___x_142_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed(lean_object* v___x_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_s_163_){
_start:
{
uint8_t v___x_4124__boxed_164_; lean_object* v_res_165_; 
v___x_4124__boxed_164_ = lean_unbox(v___x_159_);
v_res_165_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0(v___x_4124__boxed_164_, v_a_160_, v_a_161_, v_a_162_, v_s_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_171_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_170_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_215_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_215_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_215_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_215_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v_initialized_176_; 
v_initialized_176_ = lean_ctor_get_uint8(v_a_172_, sizeof(void*)*5);
lean_dec(v_a_172_);
if (v_initialized_176_ == 0)
{
lean_object* v___x_177_; 
lean_del_object(v___x_174_);
v___x_177_ = l_Lean_Meta_Grind_getHomoTheorems___redArg(v_a_168_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = l_Lean_Meta_Grind_getHomoPredTheorems___redArg(v_a_168_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l_Lean_Meta_Grind_getHomoSourceTypes___redArg(v_a_168_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___f_185_; lean_object* v___x_186_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v___x_183_ = 1;
v___x_184_ = lean_box(v___x_183_);
v___f_185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_185_, 0, v___x_184_);
lean_closure_set(v___f_185_, 1, v_a_178_);
lean_closure_set(v___f_185_, 2, v_a_180_);
lean_closure_set(v___f_185_, 3, v_a_182_);
v___x_186_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_170_, v___f_185_, v_a_166_);
return v___x_186_;
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec(v_a_180_);
lean_dec(v_a_178_);
v_a_187_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_181_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_181_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v_a_178_);
v_a_195_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_179_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_179_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_177_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_177_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_box(0);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_211_);
v___x_213_ = v___x_174_;
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
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_171_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_171_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg___boxed(lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_229_, v_a_237_, v_a_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___boxed(lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init(v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref_known(v___x_257_, 1);
v___x_258_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_259_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_258_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
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
lean_object* v_thms_264_; lean_object* v___x_266_; 
v_thms_264_ = lean_ctor_get(v_a_260_, 2);
lean_inc_ref(v_thms_264_);
lean_dec(v_a_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v_thms_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_thms_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_259_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
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
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_257_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_257_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_290_, v_a_298_, v_a_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___boxed(lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms(v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec(v_a_302_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref_known(v___x_318_, 1);
v___x_319_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_320_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_319_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_preds_325_; lean_object* v___x_327_; 
v_preds_325_ = lean_ctor_get(v_a_321_, 3);
lean_inc(v_preds_325_);
lean_dec(v_a_321_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_preds_325_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_preds_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_320_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_320_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_318_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_318_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg___boxed(lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_351_, v_a_359_, v_a_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___boxed(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds(v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_init___redArg(v_a_375_, v_a_376_, v_a_377_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref_known(v___x_379_, 1);
v___x_380_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_381_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_380_, v_a_375_, v_a_376_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_sourceTypes_386_; lean_object* v___x_388_; 
v_sourceTypes_386_ = lean_ctor_get(v_a_382_, 4);
lean_inc(v_sourceTypes_386_);
lean_dec(v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v_sourceTypes_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_sourceTypes_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_381_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_379_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_379_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_412_, v_a_420_, v_a_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___boxed(lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes(v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec(v_a_424_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(lean_object* v_e_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getSourceTypes___redArg(v_a_437_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_484_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_484_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_484_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
if (lean_obj_tag(v_a_449_) == 0)
{
lean_object* v___x_453_; 
lean_del_object(v___x_451_);
lean_inc_ref(v_e_436_);
v___x_453_ = l_Lean_Meta_Sym_inferType(v_e_436_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_471_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_471_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Expr_getAppFn(v_a_454_);
lean_dec(v_a_454_);
if (lean_obj_tag(v___x_458_) == 4)
{
lean_object* v_declName_459_; uint8_t v___x_460_; 
v_declName_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_declName_459_);
lean_dec_ref_known(v___x_458_, 2);
v___x_460_ = l_Lean_NameSet_contains(v_a_449_, v_declName_459_);
lean_dec(v_declName_459_);
lean_dec_ref_known(v_a_449_, 5);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec_ref(v_e_436_);
v___x_461_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_461_);
v___x_463_ = v___x_456_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_456_);
v___x_465_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_466_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_465_, v_e_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec_ref(v___x_458_);
lean_dec_ref_known(v_a_449_, 5);
lean_dec_ref(v_e_436_);
v___x_467_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_467_);
v___x_469_ = v___x_456_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref_known(v_a_449_, 5);
lean_dec_ref(v_e_436_);
v_a_472_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_453_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v_e_436_);
v___x_480_ = lean_box(0);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_480_);
v___x_482_ = v___x_451_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v_e_436_);
v_a_485_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_448_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_448_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm___boxed(lean_object* v_e_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec(v_a_494_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(lean_object* v_msgData_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_env_513_; lean_object* v___x_514_; lean_object* v_toCold_515_; lean_object* v_mctx_516_; lean_object* v_lctx_517_; lean_object* v_options_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_512_ = lean_st_ref_get(v___y_510_);
v_env_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_512_);
v___x_514_ = lean_st_ref_get(v___y_508_);
v_toCold_515_ = lean_ctor_get(v___y_509_, 0);
v_mctx_516_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_mctx_516_);
lean_dec(v___x_514_);
v_lctx_517_ = lean_ctor_get(v___y_507_, 2);
v_options_518_ = lean_ctor_get(v_toCold_515_, 2);
lean_inc_ref(v_options_518_);
lean_inc_ref(v_lctx_517_);
v___x_519_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_519_, 0, v_env_513_);
lean_ctor_set(v___x_519_, 1, v_mctx_516_);
lean_ctor_set(v___x_519_, 2, v_lctx_517_);
lean_ctor_set(v___x_519_, 3, v_options_518_);
v___x_520_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_msgData_506_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0___boxed(lean_object* v_msgData_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msgData_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; double v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_float_of_nat(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(lean_object* v_cls_534_, lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_ref_541_; lean_object* v___x_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_587_; 
v_ref_541_ = lean_ctor_get(v___y_538_, 2);
v___x_542_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0_spec__0(v_msg_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_587_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_587_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_587_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v_traceState_548_; lean_object* v_env_549_; lean_object* v_nextMacroScope_550_; lean_object* v_ngen_551_; lean_object* v_auxDeclNGen_552_; lean_object* v_cache_553_; lean_object* v_messages_554_; lean_object* v_infoState_555_; lean_object* v_snapshotTasks_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_586_; 
v___x_547_ = lean_st_ref_take(v___y_539_);
v_traceState_548_ = lean_ctor_get(v___x_547_, 4);
v_env_549_ = lean_ctor_get(v___x_547_, 0);
v_nextMacroScope_550_ = lean_ctor_get(v___x_547_, 1);
v_ngen_551_ = lean_ctor_get(v___x_547_, 2);
v_auxDeclNGen_552_ = lean_ctor_get(v___x_547_, 3);
v_cache_553_ = lean_ctor_get(v___x_547_, 5);
v_messages_554_ = lean_ctor_get(v___x_547_, 6);
v_infoState_555_ = lean_ctor_get(v___x_547_, 7);
v_snapshotTasks_556_ = lean_ctor_get(v___x_547_, 8);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_586_ == 0)
{
v___x_558_ = v___x_547_;
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snapshotTasks_556_);
lean_inc(v_infoState_555_);
lean_inc(v_messages_554_);
lean_inc(v_cache_553_);
lean_inc(v_traceState_548_);
lean_inc(v_auxDeclNGen_552_);
lean_inc(v_ngen_551_);
lean_inc(v_nextMacroScope_550_);
lean_inc(v_env_549_);
lean_dec(v___x_547_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint64_t v_tid_560_; lean_object* v_traces_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v_tid_560_ = lean_ctor_get_uint64(v_traceState_548_, sizeof(void*)*1);
v_traces_561_ = lean_ctor_get(v_traceState_548_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_traceState_548_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v_traceState_548_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_traces_561_);
lean_dec(v_traceState_548_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; double v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_565_ = lean_box(0);
v___x_566_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__0);
v___x_567_ = 0;
v___x_568_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__1));
v___x_569_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_569_, 0, v_cls_534_);
lean_ctor_set(v___x_569_, 1, v___x_565_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
lean_ctor_set_float(v___x_569_, sizeof(void*)*3, v___x_566_);
lean_ctor_set_float(v___x_569_, sizeof(void*)*3 + 8, v___x_566_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*3 + 16, v___x_567_);
v___x_570_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___closed__2));
v___x_571_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v_a_543_);
lean_ctor_set(v___x_571_, 2, v___x_570_);
lean_inc(v_ref_541_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_ref_541_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_PersistentArray_push___redArg(v_traces_561_, v___x_572_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_573_);
v___x_575_ = v___x_563_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_573_);
lean_ctor_set_uint64(v_reuseFailAlloc_584_, sizeof(void*)*1, v_tid_560_);
v___x_575_ = v_reuseFailAlloc_584_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_575_);
v___x_577_ = v___x_558_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_env_549_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_nextMacroScope_550_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_ngen_551_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_auxDeclNGen_552_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v_cache_553_);
lean_ctor_set(v_reuseFailAlloc_583_, 6, v_messages_554_);
lean_ctor_set(v_reuseFailAlloc_583_, 7, v_infoState_555_);
lean_ctor_set(v_reuseFailAlloc_583_, 8, v_snapshotTasks_556_);
v___x_577_ = v_reuseFailAlloc_583_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = lean_st_ref_put(v___y_539_, v___x_577_);
v___x_579_ = lean_box(0);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_579_);
v___x_581_ = v___x_545_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg___boxed(lean_object* v_cls_588_, lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_588_, v_msg_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_601_ = l_Lean_Name_append(v___x_600_, v___x_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(lean_object* v_generation_602_, lean_object* v_as_603_, size_t v_sz_604_, size_t v_i_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_lt(v_i_605_, v_sz_604_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec(v_generation_602_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_b_606_);
return v___x_619_;
}
else
{
lean_object* v_a_620_; lean_object* v_toCold_621_; lean_object* v_options_622_; lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v_inheritedTraceOptions_625_; uint8_t v_hasTrace_626_; lean_object* v___x_627_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; 
v_a_620_ = lean_array_uget_borrowed(v_as_603_, v_i_605_);
v_toCold_621_ = lean_ctor_get(v___y_615_, 0);
v_options_622_ = lean_ctor_get(v_toCold_621_, 2);
v_fst_623_ = lean_ctor_get(v_a_620_, 0);
v_snd_624_ = lean_ctor_get(v_a_620_, 1);
v_inheritedTraceOptions_625_ = lean_ctor_get(v_toCold_621_, 11);
v_hasTrace_626_ = lean_ctor_get_uint8(v_options_622_, sizeof(void*)*1);
v___x_627_ = lean_box(0);
if (v_hasTrace_626_ == 0)
{
v___y_629_ = v___y_607_;
v___y_630_ = v___y_608_;
v___y_631_ = v___y_609_;
v___y_632_ = v___y_610_;
v___y_633_ = v___y_611_;
v___y_634_ = v___y_612_;
v___y_635_ = v___y_613_;
v___y_636_ = v___y_614_;
v___y_637_ = v___y_615_;
v___y_638_ = v___y_616_;
goto v___jp_628_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_2531264644____hygCtx___hyg_2_));
v___x_646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__2);
v___x_647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_625_, v_options_622_, v___x_646_);
if (v___x_647_ == 0)
{
v___y_629_ = v___y_607_;
v___y_630_ = v___y_608_;
v___y_631_ = v___y_609_;
v___y_632_ = v___y_610_;
v___y_633_ = v___y_611_;
v___y_634_ = v___y_612_;
v___y_635_ = v___y_613_;
v___y_636_ = v___y_614_;
v___y_637_ = v___y_615_;
v___y_638_ = v___y_616_;
goto v___jp_628_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Grind_updateLastTag(v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref_known(v___x_648_, 1);
lean_inc(v_snd_624_);
v___x_649_ = l_Lean_MessageData_ofExpr(v_snd_624_);
v___x_650_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_645_, v___x_649_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_dec_ref_known(v___x_650_, 1);
v___y_629_ = v___y_607_;
v___y_630_ = v___y_608_;
v___y_631_ = v___y_609_;
v___y_632_ = v___y_610_;
v___y_633_ = v___y_611_;
v___y_634_ = v___y_612_;
v___y_635_ = v___y_613_;
v___y_636_ = v___y_614_;
v___y_637_ = v___y_615_;
v___y_638_ = v___y_616_;
goto v___jp_628_;
}
else
{
lean_dec(v_generation_602_);
return v___x_650_;
}
}
else
{
lean_dec(v_generation_602_);
return v___x_648_;
}
}
}
v___jp_628_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_box(6);
v___x_640_ = lean_box(1);
lean_inc(v_generation_602_);
lean_inc(v_snd_624_);
lean_inc(v_fst_623_);
v___x_641_ = l_Lean_Meta_Grind_addNewRawFact(v_fst_623_, v_snd_624_, v_generation_602_, v___x_639_, v___x_640_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_641_) == 0)
{
size_t v___x_642_; size_t v___x_643_; 
lean_dec_ref_known(v___x_641_, 1);
v___x_642_ = ((size_t)1ULL);
v___x_643_ = lean_usize_add(v_i_605_, v___x_642_);
v_i_605_ = v___x_643_;
v_b_606_ = v___x_627_;
goto _start;
}
else
{
lean_dec(v_generation_602_);
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___boxed(lean_object* v_generation_651_, lean_object* v_as_652_, lean_object* v_sz_653_, lean_object* v_i_654_, lean_object* v_b_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
size_t v_sz_boxed_667_; size_t v_i_boxed_668_; lean_object* v_res_669_; 
v_sz_boxed_667_ = lean_unbox_usize(v_sz_653_);
lean_dec(v_sz_653_);
v_i_boxed_668_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_651_, v_as_652_, v_sz_boxed_667_, v_i_boxed_668_, v_b_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v_as_652_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(lean_object* v_e_670_, lean_object* v_generation_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Expr_getAppFn(v_e_670_);
if (lean_obj_tag(v___x_683_) == 4)
{
lean_object* v_declName_684_; lean_object* v___x_685_; 
v_declName_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_declName_684_);
lean_dec_ref_known(v___x_683_, 2);
v___x_685_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getPreds___redArg(v_a_672_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_717_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_717_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_717_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_717_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_declName_684_, v_a_686_);
lean_dec(v_a_686_);
lean_dec(v_declName_684_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec(v_generation_671_);
lean_dec_ref(v_e_670_);
v___x_691_ = lean_box(0);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; 
lean_del_object(v___x_688_);
v___x_695_ = l_Lean_Meta_Grind_mkHomoPredInstances(v_e_670_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; size_t v_sz_698_; size_t v___x_699_; lean_object* v___x_700_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = lean_box(0);
v_sz_698_ = lean_array_size(v_a_696_);
v___x_699_ = ((size_t)0ULL);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1(v_generation_671_, v_a_696_, v_sz_698_, v___x_699_, v___x_697_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_696_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_700_, 0);
lean_dec(v_unused_708_);
v___x_702_ = v___x_700_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_dec(v___x_700_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_697_);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_697_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
return v___x_700_;
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_generation_671_);
v_a_709_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_695_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_695_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_declName_684_);
lean_dec(v_generation_671_);
lean_dec_ref(v_e_670_);
v_a_718_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_685_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_685_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v___x_683_);
lean_dec(v_generation_671_);
lean_dec_ref(v_e_670_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds___boxed(lean_object* v_e_728_, lean_object* v_generation_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_728_, v_generation_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec(v_a_730_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(lean_object* v_cls_742_, lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v_cls_742_, v_msg_743_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___boxed(lean_object* v_cls_756_, lean_object* v_msg_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0(v_cls_756_, v_msg_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
return v_res_769_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_770_, lean_object* v_i_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_array_get_size(v_keys_770_);
v___x_774_ = lean_nat_dec_lt(v_i_771_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v_i_771_);
return v___x_774_;
}
else
{
lean_object* v_k_x27_775_; size_t v___x_776_; size_t v___x_777_; uint8_t v___x_778_; 
v_k_x27_775_ = lean_array_fget_borrowed(v_keys_770_, v_i_771_);
v___x_776_ = lean_ptr_addr(v_k_772_);
v___x_777_ = lean_ptr_addr(v_k_x27_775_);
v___x_778_ = lean_usize_dec_eq(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_i_771_, v___x_779_);
lean_dec(v_i_771_);
v_i_771_ = v___x_780_;
goto _start;
}
else
{
lean_dec(v_i_771_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_782_, v_i_783_, v_k_784_);
lean_dec_ref(v_k_784_);
lean_dec_ref(v_keys_782_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(lean_object* v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_787_) == 0)
{
lean_object* v_es_790_; lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_j_794_; lean_object* v___x_795_; 
v_es_790_ = lean_ctor_get(v_x_787_, 0);
v___x_791_ = lean_box(2);
v___x_792_ = ((size_t)31ULL);
v___x_793_ = lean_usize_land(v_x_788_, v___x_792_);
v_j_794_ = lean_usize_to_nat(v___x_793_);
v___x_795_ = lean_array_get_borrowed(v___x_791_, v_es_790_, v_j_794_);
lean_dec(v_j_794_);
switch(lean_obj_tag(v___x_795_))
{
case 0:
{
lean_object* v_key_796_; size_t v___x_797_; size_t v___x_798_; uint8_t v___x_799_; 
v_key_796_ = lean_ctor_get(v___x_795_, 0);
v___x_797_ = lean_ptr_addr(v_x_789_);
v___x_798_ = lean_ptr_addr(v_key_796_);
v___x_799_ = lean_usize_dec_eq(v___x_797_, v___x_798_);
return v___x_799_;
}
case 1:
{
lean_object* v_node_800_; size_t v___x_801_; size_t v___x_802_; 
v_node_800_ = lean_ctor_get(v___x_795_, 0);
v___x_801_ = ((size_t)5ULL);
v___x_802_ = lean_usize_shift_right(v_x_788_, v___x_801_);
v_x_787_ = v_node_800_;
v_x_788_ = v___x_802_;
goto _start;
}
default: 
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
}
}
else
{
lean_object* v_ks_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_ks_805_ = lean_ctor_get(v_x_787_, 0);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_ks_805_, v___x_806_, v_x_789_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg___boxed(lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
size_t v_x_5718__boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_x_5718__boxed_811_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_res_812_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_808_, v_x_5718__boxed_811_, v_x_810_);
lean_dec_ref(v_x_810_);
lean_dec_ref(v_x_808_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; uint64_t v___x_819_; size_t v___x_820_; uint8_t v___x_821_; 
v___x_816_ = lean_ptr_addr(v_x_815_);
v___x_817_ = ((size_t)3ULL);
v___x_818_ = lean_usize_shift_right(v___x_816_, v___x_817_);
v___x_819_ = lean_usize_to_uint64(v___x_818_);
v___x_820_ = lean_uint64_to_usize(v___x_819_);
v___x_821_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_814_, v___x_820_, v_x_815_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg___boxed(lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_822_, v_x_823_);
lean_dec_ref(v_x_823_);
lean_dec_ref(v_x_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(lean_object* v_a_826_, lean_object* v___x_827_, lean_object* v_val_828_, lean_object* v_e_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
lean_inc_ref(v_e_829_);
v___x_840_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_826_, v___x_827_, v_e_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
if (lean_obj_tag(v_a_841_) == 0)
{
uint8_t v_done_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_860_; 
v_done_842_ = lean_ctor_get_uint8(v_a_841_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_860_ == 0)
{
v___x_844_ = v_a_841_;
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_a_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_860_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (v_done_842_ == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_858_; 
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_859_);
v___x_847_ = v___x_840_;
v_isShared_848_ = v_isSharedCheck_858_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_840_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_858_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_toGoalState_849_; lean_object* v_enodeMap_850_; uint8_t v___x_851_; lean_object* v___x_853_; 
v_toGoalState_849_ = lean_ctor_get(v_val_828_, 0);
v_enodeMap_850_ = lean_ctor_get(v_toGoalState_849_, 1);
v___x_851_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_enodeMap_850_, v_e_829_);
lean_dec_ref(v_e_829_);
if (v_isShared_845_ == 0)
{
v___x_853_ = v___x_844_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 0, 2);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
lean_ctor_set_uint8(v___x_853_, 0, v___x_851_);
lean_ctor_set_uint8(v___x_853_, 1, v_done_842_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_853_);
v___x_855_ = v___x_847_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_del_object(v___x_844_);
lean_dec_ref(v_e_829_);
return v___x_840_;
}
}
}
else
{
lean_dec(v_a_841_);
lean_dec_ref(v_e_829_);
return v___x_840_;
}
}
else
{
lean_dec_ref(v_e_829_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed(lean_object* v_a_861_, lean_object* v___x_862_, lean_object* v_val_863_, lean_object* v_e_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0(v_a_861_, v___x_862_, v_val_863_, v_e_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v_val_863_);
lean_dec_ref(v_a_861_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_st_ref_get(v_a_877_);
v___x_882_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_getThms___redArg(v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_892_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___x_890_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___closed__0));
v___f_888_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_888_, 0, v_a_883_);
lean_closure_set(v___f_888_, 1, v___x_887_);
lean_closure_set(v___f_888_, 2, v___x_881_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___f_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___f_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v___x_881_);
v_a_893_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_882_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_882_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg___boxed(lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_906_, v_a_914_, v_a_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___boxed(lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter(v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec(v_a_918_);
return v_res_929_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0(v_00_u03b2_934_, v_x_935_, v_x_936_);
lean_dec_ref(v_x_936_);
lean_dec_ref(v_x_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, size_t v_x_941_, lean_object* v_x_942_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___redArg(v_x_940_, v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0___boxed(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
size_t v_x_5918__boxed_948_; uint8_t v_res_949_; lean_object* v_r_950_; 
v_x_5918__boxed_948_ = lean_unbox_usize(v_x_946_);
lean_dec(v_x_946_);
v_res_949_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0(v_00_u03b2_944_, v_x_945_, v_x_5918__boxed_948_, v_x_947_);
lean_dec_ref(v_x_947_);
lean_dec_ref(v_x_945_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_951_, lean_object* v_keys_952_, lean_object* v_vals_953_, lean_object* v_heq_954_, lean_object* v_i_955_, lean_object* v_k_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___redArg(v_keys_952_, v_i_955_, v_k_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_heq_961_, lean_object* v_i_962_, lean_object* v_k_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0_spec__0_spec__1(v_00_u03b2_958_, v_keys_959_, v_vals_960_, v_heq_961_, v_i_962_, v_k_963_);
lean_dec_ref(v_k_963_);
lean_dec_ref(v_vals_960_);
lean_dec_ref(v_keys_959_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__0(lean_object* v_s_966_){
_start:
{
lean_object* v_internalized_967_; uint8_t v_initialized_968_; lean_object* v_thms_969_; lean_object* v_preds_970_; lean_object* v_sourceTypes_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_internalized_967_ = lean_ctor_get(v_s_966_, 1);
v_initialized_968_ = lean_ctor_get_uint8(v_s_966_, sizeof(void*)*5);
v_thms_969_ = lean_ctor_get(v_s_966_, 2);
v_preds_970_ = lean_ctor_get(v_s_966_, 3);
v_sourceTypes_971_ = lean_ctor_get(v_s_966_, 4);
v_isSharedCheck_979_ = !lean_is_exclusive(v_s_966_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_s_966_, 0);
lean_dec(v_unused_980_);
v___x_973_ = v_s_966_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_sourceTypes_971_);
lean_inc(v_preds_970_);
lean_inc(v_thms_969_);
lean_inc(v_internalized_967_);
lean_dec(v_s_966_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_internalized_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_thms_969_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_preds_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_sourceTypes_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*5, v_initialized_968_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(lean_object* v_snd_981_, lean_object* v_s_982_){
_start:
{
lean_object* v_persistentCache_983_; lean_object* v_internalized_984_; uint8_t v_initialized_985_; lean_object* v_thms_986_; lean_object* v_preds_987_; lean_object* v_sourceTypes_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_persistentCache_983_ = lean_ctor_get(v_snd_981_, 1);
v_internalized_984_ = lean_ctor_get(v_s_982_, 1);
v_initialized_985_ = lean_ctor_get_uint8(v_s_982_, sizeof(void*)*5);
v_thms_986_ = lean_ctor_get(v_s_982_, 2);
v_preds_987_ = lean_ctor_get(v_s_982_, 3);
v_sourceTypes_988_ = lean_ctor_get(v_s_982_, 4);
v_isSharedCheck_995_ = !lean_is_exclusive(v_s_982_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v_s_982_, 0);
lean_dec(v_unused_996_);
v___x_990_ = v_s_982_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_sourceTypes_988_);
lean_inc(v_preds_987_);
lean_inc(v_thms_986_);
lean_inc(v_internalized_984_);
lean_dec(v_s_982_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
lean_inc_ref(v_persistentCache_983_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_persistentCache_983_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_persistentCache_983_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_internalized_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_thms_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_preds_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_sourceTypes_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*5, v_initialized_985_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed(lean_object* v_snd_997_, lean_object* v_s_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1(v_snd_997_, v_s_998_);
lean_dec_ref(v_snd_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(lean_object* v_e_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter___redArg(v_a_1005_, v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_n(v_a_1014_, 2);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_a_1014_);
lean_ctor_set(v___x_1015_, 1, v_a_1014_);
v___x_1016_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1017_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1016_, v_a_1005_, v_a_1010_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___f_1019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__0));
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1016_, v___f_1019_, v_a_1005_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_cache_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec_ref_known(v___x_1020_, 1);
v_cache_1021_ = lean_ctor_get(v_a_1018_, 0);
lean_inc_ref(v_cache_1021_);
lean_dec(v_a_1018_);
v___x_1022_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1022_, 0, v_e_1004_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___closed__1));
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_4000635665____hygCtx___hyg_2_);
v___x_1026_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v_cache_1021_);
lean_ctor_set(v___x_1026_, 2, v___x_1025_);
lean_ctor_set(v___x_1026_, 3, v___x_1025_);
v___x_1027_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1022_, v___x_1015_, v___x_1023_, v___x_1026_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1062_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_fst_1029_ = lean_ctor_get(v_a_1028_, 0);
v_snd_1030_ = lean_ctor_get(v_a_1028_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1032_ = v_a_1028_;
v_isShared_1033_ = v_isSharedCheck_1062_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1030_);
lean_inc(v_fst_1029_);
lean_dec(v_a_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1062_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___f_1034_; lean_object* v___x_1035_; 
v___f_1034_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1034_, 0, v_snd_1030_);
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1016_, v___f_1034_, v_a_1005_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_1035_, 0);
lean_dec(v_unused_1053_);
v___x_1037_ = v___x_1035_;
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_1035_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1052_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
if (lean_obj_tag(v_fst_1029_) == 1)
{
lean_object* v_e_x27_1039_; lean_object* v_proof_1040_; lean_object* v___x_1042_; 
v_e_x27_1039_ = lean_ctor_get(v_fst_1029_, 0);
lean_inc_ref(v_e_x27_1039_);
v_proof_1040_ = lean_ctor_get(v_fst_1029_, 1);
lean_inc_ref(v_proof_1040_);
lean_dec_ref_known(v_fst_1029_, 2);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_proof_1040_);
lean_ctor_set(v___x_1032_, 0, v_e_x27_1039_);
v___x_1042_ = v___x_1032_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_e_x27_1039_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_proof_1040_);
v___x_1042_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1043_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_del_object(v___x_1032_);
lean_dec(v_fst_1029_);
v___x_1048_ = lean_box(0);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1048_);
v___x_1050_ = v___x_1037_;
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
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_del_object(v___x_1032_);
lean_dec(v_fst_1029_);
v_a_1054_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1035_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1035_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1027_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1027_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_a_1018_);
lean_dec_ref_known(v___x_1015_, 2);
lean_dec_ref(v_e_1004_);
v_a_1071_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1020_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1020_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref_known(v___x_1015_, 2);
lean_dec_ref(v_e_1004_);
v_a_1079_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1017_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1017_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_e_1004_);
v_a_1087_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1013_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1013_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg___boxed(lean_object* v_e_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(lean_object* v_e_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1105_, v_a_1106_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___boxed(lean_object* v_e_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f(v_e_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec(v_a_1119_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v_ks_1135_; lean_object* v_vs_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1162_; 
v_ks_1135_ = lean_ctor_get(v_x_1131_, 0);
v_vs_1136_ = lean_ctor_get(v_x_1131_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1131_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1138_ = v_x_1131_;
v_isShared_1139_ = v_isSharedCheck_1162_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_vs_1136_);
lean_inc(v_ks_1135_);
lean_dec(v_x_1131_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1162_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_array_get_size(v_ks_1135_);
v___x_1141_ = lean_nat_dec_lt(v_x_1132_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
lean_dec(v_x_1132_);
v___x_1142_ = lean_array_push(v_ks_1135_, v_x_1133_);
v___x_1143_ = lean_array_push(v_vs_1136_, v_x_1134_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1143_);
lean_ctor_set(v___x_1138_, 0, v___x_1142_);
v___x_1145_ = v___x_1138_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v_k_x27_1147_; size_t v___x_1148_; size_t v___x_1149_; uint8_t v___x_1150_; 
v_k_x27_1147_ = lean_array_fget_borrowed(v_ks_1135_, v_x_1132_);
v___x_1148_ = lean_ptr_addr(v_x_1133_);
v___x_1149_ = lean_ptr_addr(v_k_x27_1147_);
v___x_1150_ = lean_usize_dec_eq(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; 
if (v_isShared_1139_ == 0)
{
v___x_1152_ = v___x_1138_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_ks_1135_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_vs_1136_);
v___x_1152_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_x_1132_, v___x_1153_);
lean_dec(v_x_1132_);
v_x_1131_ = v___x_1152_;
v_x_1132_ = v___x_1154_;
goto _start;
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1157_ = lean_array_fset(v_ks_1135_, v_x_1132_, v_x_1133_);
v___x_1158_ = lean_array_fset(v_vs_1136_, v_x_1132_, v_x_1134_);
lean_dec(v_x_1132_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1158_);
lean_ctor_set(v___x_1138_, 0, v___x_1157_);
v___x_1160_ = v___x_1138_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1163_, lean_object* v_k_1164_, lean_object* v_v_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1163_, v___x_1166_, v_k_1164_, v_v_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(lean_object* v_x_1169_, size_t v_x_1170_, size_t v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v_es_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v_j_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_es_1174_ = lean_ctor_get(v_x_1169_, 0);
v___x_1175_ = ((size_t)31ULL);
v___x_1176_ = lean_usize_land(v_x_1170_, v___x_1175_);
v_j_1177_ = lean_usize_to_nat(v___x_1176_);
v___x_1178_ = lean_array_get_size(v_es_1174_);
v___x_1179_ = lean_nat_dec_lt(v_j_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec(v_j_1177_);
lean_dec(v_x_1173_);
lean_dec_ref(v_x_1172_);
return v_x_1169_;
}
else
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1220_; 
lean_inc_ref(v_es_1174_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_x_1169_, 0);
lean_dec(v_unused_1221_);
v___x_1181_ = v_x_1169_;
v_isShared_1182_ = v_isSharedCheck_1220_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_x_1169_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1220_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_v_1183_; lean_object* v___x_1184_; lean_object* v_xs_x27_1185_; lean_object* v___y_1187_; 
v_v_1183_ = lean_array_fget(v_es_1174_, v_j_1177_);
v___x_1184_ = lean_box(0);
v_xs_x27_1185_ = lean_array_fset(v_es_1174_, v_j_1177_, v___x_1184_);
switch(lean_obj_tag(v_v_1183_))
{
case 0:
{
lean_object* v_key_1192_; lean_object* v_val_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1205_; 
v_key_1192_ = lean_ctor_get(v_v_1183_, 0);
v_val_1193_ = lean_ctor_get(v_v_1183_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_v_1183_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1195_ = v_v_1183_;
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_val_1193_);
lean_inc(v_key_1192_);
lean_dec(v_v_1183_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
size_t v___x_1197_; size_t v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = lean_ptr_addr(v_x_1172_);
v___x_1198_ = lean_ptr_addr(v_key_1192_);
v___x_1199_ = lean_usize_dec_eq(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1195_);
v___x_1200_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1192_, v_val_1193_, v_x_1172_, v_x_1173_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
v___y_1187_ = v___x_1201_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1203_; 
lean_dec(v_val_1193_);
lean_dec(v_key_1192_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_x_1173_);
lean_ctor_set(v___x_1195_, 0, v_x_1172_);
v___x_1203_ = v___x_1195_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_x_1172_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_x_1173_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v___y_1187_ = v___x_1203_;
goto v___jp_1186_;
}
}
}
}
case 1:
{
lean_object* v_node_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1218_; 
v_node_1206_ = lean_ctor_get(v_v_1183_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_v_1183_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1208_ = v_v_1183_;
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_node_1206_);
lean_dec(v_v_1183_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1210_ = ((size_t)5ULL);
v___x_1211_ = lean_usize_shift_right(v_x_1170_, v___x_1210_);
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_x_1171_, v___x_1212_);
v___x_1214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_node_1206_, v___x_1211_, v___x_1213_, v_x_1172_, v_x_1173_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1214_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v___y_1187_ = v___x_1216_;
goto v___jp_1186_;
}
}
}
default: 
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_x_1172_);
lean_ctor_set(v___x_1219_, 1, v_x_1173_);
v___y_1187_ = v___x_1219_;
goto v___jp_1186_;
}
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_array_fset(v_xs_x27_1185_, v_j_1177_, v___y_1187_);
lean_dec(v_j_1177_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1188_);
v___x_1190_ = v___x_1181_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
else
{
lean_object* v_ks_1222_; lean_object* v_vs_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1241_; 
v_ks_1222_ = lean_ctor_get(v_x_1169_, 0);
v_vs_1223_ = lean_ctor_get(v_x_1169_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1225_ = v_x_1169_;
v_isShared_1226_ = v_isSharedCheck_1241_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_vs_1223_);
lean_inc(v_ks_1222_);
lean_dec(v_x_1169_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1241_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_ks_1222_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_vs_1223_);
v___x_1228_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v_newNode_1229_; size_t v___x_1230_; uint8_t v___x_1231_; 
v_newNode_1229_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v___x_1228_, v_x_1172_, v_x_1173_);
v___x_1230_ = ((size_t)7ULL);
v___x_1231_ = lean_usize_dec_le(v___x_1230_, v_x_1171_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1232_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1229_);
v___x_1233_ = lean_unsigned_to_nat(4u);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
lean_dec(v___x_1232_);
if (v___x_1234_ == 0)
{
lean_object* v_ks_1235_; lean_object* v_vs_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_ks_1235_ = lean_ctor_get(v_newNode_1229_, 0);
lean_inc_ref(v_ks_1235_);
v_vs_1236_ = lean_ctor_get(v_newNode_1229_, 1);
lean_inc_ref(v_vs_1236_);
lean_dec_ref(v_newNode_1229_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___closed__0);
v___x_1239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_x_1171_, v_ks_1235_, v_vs_1236_, v___x_1237_, v___x_1238_);
lean_dec_ref(v_vs_1236_);
lean_dec_ref(v_ks_1235_);
return v___x_1239_;
}
else
{
return v_newNode_1229_;
}
}
else
{
return v_newNode_1229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_1242_, lean_object* v_keys_1243_, lean_object* v_vals_1244_, lean_object* v_i_1245_, lean_object* v_entries_1246_){
_start:
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_array_get_size(v_keys_1243_);
v___x_1248_ = lean_nat_dec_lt(v_i_1245_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec(v_i_1245_);
return v_entries_1246_;
}
else
{
lean_object* v_k_1249_; lean_object* v_v_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; uint64_t v___x_1254_; size_t v_h_1255_; size_t v___x_1256_; lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; size_t v_h_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_k_1249_ = lean_array_fget_borrowed(v_keys_1243_, v_i_1245_);
v_v_1250_ = lean_array_fget_borrowed(v_vals_1244_, v_i_1245_);
v___x_1251_ = lean_ptr_addr(v_k_1249_);
v___x_1252_ = ((size_t)3ULL);
v___x_1253_ = lean_usize_shift_right(v___x_1251_, v___x_1252_);
v___x_1254_ = lean_usize_to_uint64(v___x_1253_);
v_h_1255_ = lean_uint64_to_usize(v___x_1254_);
v___x_1256_ = ((size_t)5ULL);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_sub(v_depth_1242_, v___x_1258_);
v___x_1260_ = lean_usize_mul(v___x_1256_, v___x_1259_);
v_h_1261_ = lean_usize_shift_right(v_h_1255_, v___x_1260_);
v___x_1262_ = lean_nat_add(v_i_1245_, v___x_1257_);
lean_dec(v_i_1245_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
v___x_1263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_entries_1246_, v_h_1261_, v_depth_1242_, v_k_1249_, v_v_1250_);
v_i_1245_ = v___x_1262_;
v_entries_1246_ = v___x_1263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1265_, lean_object* v_keys_1266_, lean_object* v_vals_1267_, lean_object* v_i_1268_, lean_object* v_entries_1269_){
_start:
{
size_t v_depth_boxed_1270_; lean_object* v_res_1271_; 
v_depth_boxed_1270_ = lean_unbox_usize(v_depth_1265_);
lean_dec(v_depth_1265_);
v_res_1271_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1270_, v_keys_1266_, v_vals_1267_, v_i_1268_, v_entries_1269_);
lean_dec_ref(v_vals_1267_);
lean_dec_ref(v_keys_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
size_t v_x_28751__boxed_1277_; size_t v_x_28752__boxed_1278_; lean_object* v_res_1279_; 
v_x_28751__boxed_1277_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_x_28752__boxed_1278_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_res_1279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1272_, v_x_28751__boxed_1277_, v_x_28752__boxed_1278_, v_x_1275_, v_x_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; uint64_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1283_ = lean_ptr_addr(v_x_1281_);
v___x_1284_ = ((size_t)3ULL);
v___x_1285_ = lean_usize_shift_right(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_usize_to_uint64(v___x_1285_);
v___x_1287_ = lean_uint64_to_usize(v___x_1286_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1280_, v___x_1287_, v___x_1288_, v_x_1281_, v_x_1282_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0(lean_object* v_e_1290_, lean_object* v_s_1291_){
_start:
{
lean_object* v_cache_1292_; lean_object* v_internalized_1293_; uint8_t v_initialized_1294_; lean_object* v_thms_1295_; lean_object* v_preds_1296_; lean_object* v_sourceTypes_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1306_; 
v_cache_1292_ = lean_ctor_get(v_s_1291_, 0);
v_internalized_1293_ = lean_ctor_get(v_s_1291_, 1);
v_initialized_1294_ = lean_ctor_get_uint8(v_s_1291_, sizeof(void*)*5);
v_thms_1295_ = lean_ctor_get(v_s_1291_, 2);
v_preds_1296_ = lean_ctor_get(v_s_1291_, 3);
v_sourceTypes_1297_ = lean_ctor_get(v_s_1291_, 4);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_s_1291_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1299_ = v_s_1291_;
v_isShared_1300_ = v_isSharedCheck_1306_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_sourceTypes_1297_);
lean_inc(v_preds_1296_);
lean_inc(v_thms_1295_);
lean_inc(v_internalized_1293_);
lean_inc(v_cache_1292_);
lean_dec(v_s_1291_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1306_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1301_ = lean_box(0);
v___x_1302_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_internalized_1293_, v_e_1290_, v___x_1301_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___x_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_cache_1292_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_thms_1295_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_preds_1296_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_sourceTypes_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1305_, sizeof(void*)*5, v_initialized_1294_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__1___closed__1));
v___x_1312_ = l_Lean_Name_append(v___x_1311_, v___x_1310_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__3));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg(lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1319_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1448_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1448_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1448_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint8_t v_hom_1333_; 
v_hom_1333_ = lean_ctor_get_uint8(v_a_1329_, sizeof(void*)*14 + 24);
lean_dec(v_a_1329_);
if (v_hom_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec_ref(v_e_1316_);
v___x_1334_ = lean_box(0);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1334_);
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
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
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_internalize___redArg___closed__1));
v___x_1339_ = l_Lean_Expr_isAppOf(v_e_1316_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_del_object(v___x_1331_);
v___x_1340_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_1341_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_1340_, v_a_1317_, v_a_1325_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1435_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1435_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1435_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_internalized_1346_; uint8_t v___x_1347_; 
v_internalized_1346_ = lean_ctor_get(v_a_1342_, 1);
lean_inc_ref(v_internalized_1346_);
lean_dec(v_a_1342_);
v___x_1347_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_mkRewriter_spec__0___redArg(v_internalized_1346_, v_e_1316_);
lean_dec_ref(v_internalized_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___f_1348_; lean_object* v___x_1349_; 
lean_del_object(v___x_1344_);
lean_inc_ref(v_e_1316_);
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Homo_internalize___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1348_, 0, v_e_1316_);
v___x_1349_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1340_, v___f_1348_, v_a_1317_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1350_; 
lean_dec_ref_known(v___x_1349_, 1);
lean_inc_ref(v_e_1316_);
v___x_1350_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_markSourceTerm(v_e_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref_known(v___x_1350_, 1);
v___x_1351_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
lean_inc_ref(v_e_1316_);
v___x_1353_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_e_1316_, v_a_1317_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
if (lean_obj_tag(v_a_1354_) == 1)
{
lean_object* v_val_1355_; lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1413_; 
v_val_1355_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v_a_1354_, 1);
v_fst_1356_ = lean_ctor_get(v_val_1355_, 0);
v_snd_1357_ = lean_ctor_get(v_val_1355_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_val_1355_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1359_ = v_val_1355_;
v_isShared_1360_ = v_isSharedCheck_1413_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_inc(v_fst_1356_);
lean_dec(v_val_1355_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1413_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; 
lean_inc(v_a_1326_);
lean_inc_ref(v_a_1325_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc(v_a_1317_);
v___x_1361_ = lean_grind_preprocess(v_fst_1356_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_n(v_a_1362_, 2);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l_Lean_Meta_Simp_Result_getProof(v_a_1362_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l_Lean_Meta_mkEqTrans(v_snd_1357_, v_a_1364_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v_expr_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v_expr_1367_ = lean_ctor_get(v_a_1362_, 0);
lean_inc_ref_n(v_expr_1367_, 2);
lean_dec(v_a_1362_);
v___x_1368_ = lean_box(0);
lean_inc(v_a_1326_);
lean_inc_ref(v_a_1325_);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
lean_inc(v_a_1320_);
lean_inc_ref(v_a_1319_);
lean_inc(v_a_1318_);
lean_inc(v_a_1317_);
v___x_1369_ = lean_grind_internalize(v_expr_1367_, v_a_1352_, v___x_1368_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_toCold_1370_; lean_object* v_options_1371_; uint8_t v_hasTrace_1372_; 
lean_dec_ref_known(v___x_1369_, 1);
v_toCold_1370_ = lean_ctor_get(v_a_1325_, 0);
v_options_1371_ = lean_ctor_get(v_toCold_1370_, 2);
v_hasTrace_1372_ = lean_ctor_get_uint8(v_options_1371_, sizeof(void*)*1);
if (v_hasTrace_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_del_object(v___x_1359_);
v___x_1373_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1316_, v_expr_1367_, v_a_1366_, v___x_1347_, v_a_1317_, v_a_1319_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1373_;
}
else
{
lean_object* v_inheritedTraceOptions_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_inheritedTraceOptions_1374_ = lean_ctor_get(v_toCold_1370_, 11);
v___x_1375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2);
v___x_1377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1374_, v_options_1371_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1359_);
v___x_1378_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1316_, v_expr_1367_, v_a_1366_, v___x_1347_, v_a_1317_, v_a_1319_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Grind_updateLastTag(v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref_known(v___x_1379_, 1);
lean_inc_ref(v_e_1316_);
v___x_1380_ = l_Lean_MessageData_ofExpr(v_e_1316_);
v___x_1381_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4);
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 7);
lean_ctor_set(v___x_1359_, 1, v___x_1381_);
lean_ctor_set(v___x_1359_, 0, v___x_1380_);
v___x_1383_ = v___x_1359_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_inc_ref(v_expr_1367_);
v___x_1384_ = l_Lean_MessageData_ofExpr(v_expr_1367_);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1375_, v___x_1385_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1387_; 
lean_dec_ref_known(v___x_1386_, 1);
v___x_1387_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1316_, v_expr_1367_, v_a_1366_, v___x_1347_, v_a_1317_, v_a_1319_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1387_;
}
else
{
lean_dec_ref(v_expr_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_e_1316_);
return v___x_1386_;
}
}
}
else
{
lean_dec_ref(v_expr_1367_);
lean_dec(v_a_1366_);
lean_del_object(v___x_1359_);
lean_dec_ref(v_e_1316_);
return v___x_1379_;
}
}
}
}
else
{
lean_dec_ref(v_expr_1367_);
lean_dec(v_a_1366_);
lean_del_object(v___x_1359_);
lean_dec_ref(v_e_1316_);
return v___x_1369_;
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec(v_a_1362_);
lean_del_object(v___x_1359_);
lean_dec(v_a_1352_);
lean_dec_ref(v_e_1316_);
v_a_1389_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1365_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1365_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_a_1362_);
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec(v_a_1352_);
lean_dec_ref(v_e_1316_);
v_a_1397_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1363_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1363_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec(v_a_1352_);
lean_dec_ref(v_e_1316_);
v_a_1405_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1361_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1361_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v___x_1414_; 
lean_dec(v_a_1354_);
v___x_1414_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds(v_e_1316_, v_a_1352_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1414_;
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_a_1352_);
lean_dec_ref(v_e_1316_);
v_a_1415_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1353_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1353_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v_e_1316_);
v_a_1423_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1351_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1351_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_dec_ref(v_e_1316_);
return v___x_1350_;
}
}
else
{
lean_dec_ref(v_e_1316_);
return v___x_1349_;
}
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec_ref(v_e_1316_);
v___x_1431_ = lean_box(0);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1431_);
v___x_1433_ = v___x_1344_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_e_1316_);
v_a_1436_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1341_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1341_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref(v_e_1316_);
v___x_1444_ = lean_box(0);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1444_);
v___x_1446_ = v___x_1331_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v_e_1316_);
v_a_1449_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1328_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1328_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___redArg___boxed(lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec(v_a_1458_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize(lean_object* v_e_1470_, lean_object* v___parent_x3f_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Meta_Grind_Homo_internalize___redArg(v_e_1470_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_internalize___boxed(lean_object* v_e_1484_, lean_object* v___parent_x3f_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_Grind_Homo_internalize(v_e_1484_, v___parent_x3f_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec(v___parent_x3f_1485_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0(lean_object* v_00_u03b2_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0___redArg(v_x_1499_, v_x_1500_, v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(lean_object* v_00_u03b2_1503_, lean_object* v_x_1504_, size_t v_x_1505_, size_t v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___redArg(v_x_1504_, v_x_1505_, v_x_1506_, v_x_1507_, v_x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
size_t v_x_29252__boxed_1516_; size_t v_x_29253__boxed_1517_; lean_object* v_res_1518_; 
v_x_29252__boxed_1516_ = lean_unbox_usize(v_x_1512_);
lean_dec(v_x_1512_);
v_x_29253__boxed_1517_ = lean_unbox_usize(v_x_1513_);
lean_dec(v_x_1513_);
v_res_1518_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0(v_00_u03b2_1510_, v_x_1511_, v_x_29252__boxed_1516_, v_x_29253__boxed_1517_, v_x_1514_, v_x_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1519_, lean_object* v_n_1520_, lean_object* v_k_1521_, lean_object* v_v_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1___redArg(v_n_1520_, v_k_1521_, v_v_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1524_, size_t v_depth_1525_, lean_object* v_keys_1526_, lean_object* v_vals_1527_, lean_object* v_heq_1528_, lean_object* v_i_1529_, lean_object* v_entries_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___redArg(v_depth_1525_, v_keys_1526_, v_vals_1527_, v_i_1529_, v_entries_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1532_, lean_object* v_depth_1533_, lean_object* v_keys_1534_, lean_object* v_vals_1535_, lean_object* v_heq_1536_, lean_object* v_i_1537_, lean_object* v_entries_1538_){
_start:
{
size_t v_depth_boxed_1539_; lean_object* v_res_1540_; 
v_depth_boxed_1539_ = lean_unbox_usize(v_depth_1533_);
lean_dec(v_depth_1533_);
v_res_1540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__2(v_00_u03b2_1532_, v_depth_boxed_1539_, v_keys_1534_, v_vals_1535_, v_heq_1536_, v_i_1537_, v_entries_1538_);
lean_dec_ref(v_vals_1535_);
lean_dec_ref(v_keys_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Homo_internalize_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1542_, v_x_1543_, v_x_1544_, v_x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq(lean_object* v_a_1547_, lean_object* v_b_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1551_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1708_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1708_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1708_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
uint8_t v_hom_1565_; 
v_hom_1565_ = lean_ctor_get_uint8(v_a_1561_, sizeof(void*)*14 + 24);
lean_dec(v_a_1561_);
if (v_hom_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v___x_1566_ = lean_box(0);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
else
{
lean_object* v___x_1570_; 
lean_del_object(v___x_1563_);
lean_inc_ref(v_b_1548_);
lean_inc_ref(v_a_1547_);
v___x_1570_ = l_Lean_Meta_Grind_hasSameType(v_a_1547_, v_b_1548_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1699_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1699_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1699_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; 
v___x_1575_ = lean_unbox(v_a_1571_);
lean_dec(v_a_1571_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v___x_1576_ = lean_box(0);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
else
{
lean_object* v___x_1580_; 
lean_del_object(v___x_1573_);
lean_inc_ref(v_b_1548_);
lean_inc_ref(v_a_1547_);
v___x_1580_ = l_Lean_Meta_mkEq(v_a_1547_, v_b_1548_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = l_Lean_Meta_Sym_shareCommon(v_a_1581_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc_n(v_a_1583_, 2);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_1583_, v_a_1549_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1674_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1674_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1674_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
if (lean_obj_tag(v_a_1585_) == 1)
{
lean_object* v_val_1589_; lean_object* v_fst_1590_; lean_object* v_snd_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1587_);
v_val_1589_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_a_1585_, 1);
v_fst_1590_ = lean_ctor_get(v_val_1589_, 0);
v_snd_1591_ = lean_ctor_get(v_val_1589_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_val_1589_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1593_ = v_val_1589_;
v_isShared_1594_ = v_isSharedCheck_1669_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snd_1591_);
lean_inc(v_fst_1590_);
lean_dec(v_val_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1669_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; 
lean_inc(v_a_1558_);
lean_inc_ref(v_a_1557_);
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
lean_inc(v_a_1554_);
lean_inc_ref(v_a_1553_);
lean_inc(v_a_1552_);
lean_inc_ref(v_a_1551_);
lean_inc(v_a_1550_);
lean_inc(v_a_1549_);
lean_inc_ref(v_b_1548_);
lean_inc_ref(v_a_1547_);
v___x_1595_ = lean_grind_mk_eq_proof(v_a_1547_, v_b_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = l_Lean_Meta_mkEqMP(v_snd_1591_, v_a_1596_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___x_1614_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v___x_1614_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1547_, v_a_1549_);
lean_dec_ref(v_a_1547_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1616_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1548_, v_a_1549_);
lean_dec_ref(v_b_1548_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___y_1619_; uint8_t v___x_1636_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1636_ = lean_nat_dec_le(v_a_1615_, v_a_1617_);
if (v___x_1636_ == 0)
{
lean_dec(v_a_1617_);
v___y_1619_ = v_a_1615_;
goto v___jp_1618_;
}
else
{
lean_dec(v_a_1615_);
v___y_1619_ = v_a_1617_;
goto v___jp_1618_;
}
v___jp_1618_:
{
lean_object* v_toCold_1620_; lean_object* v_options_1621_; uint8_t v_hasTrace_1622_; 
v_toCold_1620_ = lean_ctor_get(v_a_1557_, 0);
v_options_1621_ = lean_ctor_get(v_toCold_1620_, 2);
v_hasTrace_1622_ = lean_ctor_get_uint8(v_options_1621_, sizeof(void*)*1);
if (v_hasTrace_1622_ == 0)
{
lean_del_object(v___x_1593_);
lean_dec(v_a_1583_);
v___y_1600_ = v___y_1619_;
v___y_1601_ = v_a_1549_;
v___y_1602_ = v_a_1550_;
v___y_1603_ = v_a_1551_;
v___y_1604_ = v_a_1552_;
v___y_1605_ = v_a_1553_;
v___y_1606_ = v_a_1554_;
v___y_1607_ = v_a_1555_;
v___y_1608_ = v_a_1556_;
v___y_1609_ = v_a_1557_;
v___y_1610_ = v_a_1558_;
goto v___jp_1599_;
}
else
{
lean_object* v_inheritedTraceOptions_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_inheritedTraceOptions_1623_ = lean_ctor_get(v_toCold_1620_, 11);
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1625_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2);
v___x_1626_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1623_, v_options_1621_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_del_object(v___x_1593_);
lean_dec(v_a_1583_);
v___y_1600_ = v___y_1619_;
v___y_1601_ = v_a_1549_;
v___y_1602_ = v_a_1550_;
v___y_1603_ = v_a_1551_;
v___y_1604_ = v_a_1552_;
v___y_1605_ = v_a_1553_;
v___y_1606_ = v_a_1554_;
v___y_1607_ = v_a_1555_;
v___y_1608_ = v_a_1556_;
v___y_1609_ = v_a_1557_;
v___y_1610_ = v_a_1558_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Meta_Grind_updateLastTag(v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec_ref_known(v___x_1627_, 1);
v___x_1628_ = l_Lean_MessageData_ofExpr(v_a_1583_);
v___x_1629_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 7);
lean_ctor_set(v___x_1593_, 1, v___x_1629_);
lean_ctor_set(v___x_1593_, 0, v___x_1628_);
v___x_1631_ = v___x_1593_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_inc(v_fst_1590_);
v___x_1632_ = l_Lean_MessageData_ofExpr(v_fst_1590_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1624_, v___x_1633_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref_known(v___x_1634_, 1);
v___y_1600_ = v___y_1619_;
v___y_1601_ = v_a_1549_;
v___y_1602_ = v_a_1550_;
v___y_1603_ = v_a_1551_;
v___y_1604_ = v_a_1552_;
v___y_1605_ = v_a_1553_;
v___y_1606_ = v_a_1554_;
v___y_1607_ = v_a_1555_;
v___y_1608_ = v_a_1556_;
v___y_1609_ = v_a_1557_;
v___y_1610_ = v_a_1558_;
goto v___jp_1599_;
}
else
{
lean_dec(v___y_1619_);
lean_dec(v_a_1598_);
lean_dec(v_fst_1590_);
return v___x_1634_;
}
}
}
else
{
lean_dec(v___y_1619_);
lean_dec(v_a_1598_);
lean_del_object(v___x_1593_);
lean_dec(v_fst_1590_);
lean_dec(v_a_1583_);
return v___x_1627_;
}
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_a_1615_);
lean_dec(v_a_1598_);
lean_del_object(v___x_1593_);
lean_dec(v_fst_1590_);
lean_dec(v_a_1583_);
v_a_1637_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1616_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1616_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1598_);
lean_del_object(v___x_1593_);
lean_dec(v_fst_1590_);
lean_dec(v_a_1583_);
lean_dec_ref(v_b_1548_);
v_a_1645_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1614_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1614_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
v___jp_1599_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = lean_box(6);
v___x_1612_ = lean_box(1);
v___x_1613_ = l_Lean_Meta_Grind_addNewRawFact(v_a_1598_, v_fst_1590_, v___y_1600_, v___x_1611_, v___x_1612_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1613_;
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_del_object(v___x_1593_);
lean_dec(v_fst_1590_);
lean_dec(v_a_1583_);
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1653_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1597_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1597_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_del_object(v___x_1593_);
lean_dec(v_snd_1591_);
lean_dec(v_fst_1590_);
lean_dec(v_a_1583_);
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1661_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1595_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1595_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1583_);
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v___x_1670_ = lean_box(0);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1670_);
v___x_1672_ = v___x_1587_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_a_1583_);
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1675_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1584_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1584_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1683_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1582_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1582_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1691_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1580_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1580_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1700_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1570_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1570_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v_b_1548_);
lean_dec_ref(v_a_1547_);
v_a_1709_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1560_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1560_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewEq___boxed(lean_object* v_a_1717_, lean_object* v_b_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Meta_Grind_Homo_processNewEq(v_a_1717_, v_b_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec(v_a_1719_);
return v_res_1730_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = ((lean_object*)(l_Lean_Meta_Grind_Homo_processNewDiseq___closed__1));
v___x_1736_ = l_Lean_mkConst(v___x_1735_, v___x_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq(lean_object* v_a_1737_, lean_object* v_b_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1741_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1912_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1912_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1912_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
uint8_t v_hom_1755_; 
v_hom_1755_ = lean_ctor_get_uint8(v_a_1751_, sizeof(void*)*14 + 24);
lean_dec(v_a_1751_);
if (v_hom_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v___x_1756_ = lean_box(0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
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
lean_object* v___x_1760_; 
lean_del_object(v___x_1753_);
lean_inc_ref(v_b_1738_);
lean_inc_ref(v_a_1737_);
v___x_1760_ = l_Lean_Meta_Grind_hasSameType(v_a_1737_, v_b_1738_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1903_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1903_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1903_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
uint8_t v___x_1765_; 
v___x_1765_ = lean_unbox(v_a_1761_);
lean_dec(v_a_1761_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v___x_1766_ = lean_box(0);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
else
{
lean_object* v___x_1770_; 
lean_del_object(v___x_1763_);
lean_inc_ref(v_b_1738_);
lean_inc_ref(v_a_1737_);
v___x_1770_ = l_Lean_Meta_mkEq(v_a_1737_, v_b_1738_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_Meta_Sym_shareCommon(v_a_1771_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc_n(v_a_1773_, 2);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_applyHomo_x3f___redArg(v_a_1773_, v_a_1739_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1878_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1878_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1878_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
if (lean_obj_tag(v_a_1775_) == 1)
{
lean_object* v_val_1779_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1873_; 
lean_del_object(v___x_1777_);
v_val_1779_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v_a_1775_, 1);
v_fst_1780_ = lean_ctor_get(v_val_1779_, 0);
v_snd_1781_ = lean_ctor_get(v_val_1779_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_val_1779_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1783_ = v_val_1779_;
v_isShared_1784_ = v_isSharedCheck_1873_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_snd_1781_);
lean_inc(v_fst_1780_);
lean_dec(v_val_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1873_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; 
lean_inc_ref(v_b_1738_);
lean_inc_ref(v_a_1737_);
v___x_1785_ = l_Lean_Meta_Grind_mkDiseqProof(v_a_1737_, v_b_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2, &l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2_once, _init_l_Lean_Meta_Grind_Homo_processNewDiseq___closed__2);
v___x_1788_ = l_Lean_Meta_mkCongrArg(v___x_1787_, v_snd_1781_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l_Lean_Meta_mkEqMP(v_a_1789_, v_a_1786_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___x_1808_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1808_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1737_, v_a_1739_);
lean_dec_ref(v_a_1737_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_1738_, v_a_1739_);
lean_dec_ref(v_b_1738_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___y_1813_; uint8_t v___x_1832_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1832_ = lean_nat_dec_le(v_a_1809_, v_a_1811_);
if (v___x_1832_ == 0)
{
lean_dec(v_a_1811_);
v___y_1813_ = v_a_1809_;
goto v___jp_1812_;
}
else
{
lean_dec(v_a_1809_);
v___y_1813_ = v_a_1811_;
goto v___jp_1812_;
}
v___jp_1812_:
{
lean_object* v_toCold_1814_; lean_object* v_options_1815_; uint8_t v_hasTrace_1816_; 
v_toCold_1814_ = lean_ctor_get(v_a_1747_, 0);
v_options_1815_ = lean_ctor_get(v_toCold_1814_, 2);
v_hasTrace_1816_ = lean_ctor_get_uint8(v_options_1815_, sizeof(void*)*1);
if (v_hasTrace_1816_ == 0)
{
lean_del_object(v___x_1783_);
lean_dec(v_a_1773_);
v___y_1793_ = v___y_1813_;
v___y_1794_ = v_a_1739_;
v___y_1795_ = v_a_1740_;
v___y_1796_ = v_a_1741_;
v___y_1797_ = v_a_1742_;
v___y_1798_ = v_a_1743_;
v___y_1799_ = v_a_1744_;
v___y_1800_ = v_a_1745_;
v___y_1801_ = v_a_1746_;
v___y_1802_ = v_a_1747_;
v___y_1803_ = v_a_1748_;
goto v___jp_1792_;
}
else
{
lean_object* v_inheritedTraceOptions_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_inheritedTraceOptions_1817_ = lean_ctor_get(v_toCold_1814_, 11);
v___x_1818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3754153130____hygCtx___hyg_2_));
v___x_1819_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__2);
v___x_1820_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1817_, v_options_1815_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_del_object(v___x_1783_);
lean_dec(v_a_1773_);
v___y_1793_ = v___y_1813_;
v___y_1794_ = v_a_1739_;
v___y_1795_ = v_a_1740_;
v___y_1796_ = v_a_1741_;
v___y_1797_ = v_a_1742_;
v___y_1798_ = v_a_1743_;
v___y_1799_ = v_a_1744_;
v___y_1800_ = v_a_1745_;
v___y_1801_ = v_a_1746_;
v___y_1802_ = v_a_1747_;
v___y_1803_ = v_a_1748_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Meta_Grind_updateLastTag(v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
lean_dec_ref_known(v___x_1821_, 1);
v___x_1822_ = l_Lean_mkNot(v_a_1773_);
v___x_1823_ = l_Lean_MessageData_ofExpr(v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4, &l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Homo_internalize___redArg___closed__4);
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 7);
lean_ctor_set(v___x_1783_, 1, v___x_1824_);
lean_ctor_set(v___x_1783_, 0, v___x_1823_);
v___x_1826_ = v___x_1783_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_inc(v_fst_1780_);
v___x_1827_ = l_Lean_mkNot(v_fst_1780_);
v___x_1828_ = l_Lean_MessageData_ofExpr(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1826_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_firePreds_spec__0___redArg(v___x_1818_, v___x_1829_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_dec_ref_known(v___x_1830_, 1);
v___y_1793_ = v___y_1813_;
v___y_1794_ = v_a_1739_;
v___y_1795_ = v_a_1740_;
v___y_1796_ = v_a_1741_;
v___y_1797_ = v_a_1742_;
v___y_1798_ = v_a_1743_;
v___y_1799_ = v_a_1744_;
v___y_1800_ = v_a_1745_;
v___y_1801_ = v_a_1746_;
v___y_1802_ = v_a_1747_;
v___y_1803_ = v_a_1748_;
goto v___jp_1792_;
}
else
{
lean_dec(v___y_1813_);
lean_dec(v_a_1791_);
lean_dec(v_fst_1780_);
return v___x_1830_;
}
}
}
else
{
lean_dec(v___y_1813_);
lean_dec(v_a_1791_);
lean_del_object(v___x_1783_);
lean_dec(v_fst_1780_);
lean_dec(v_a_1773_);
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_a_1809_);
lean_dec(v_a_1791_);
lean_del_object(v___x_1783_);
lean_dec(v_fst_1780_);
lean_dec(v_a_1773_);
v_a_1833_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1810_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1810_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1791_);
lean_del_object(v___x_1783_);
lean_dec(v_fst_1780_);
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1738_);
v_a_1841_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1808_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1808_);
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
v___jp_1792_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1804_ = l_Lean_mkNot(v_fst_1780_);
v___x_1805_ = lean_box(6);
v___x_1806_ = lean_box(1);
v___x_1807_ = l_Lean_Meta_Grind_addNewRawFact(v_a_1791_, v___x_1804_, v___y_1793_, v___x_1805_, v___x_1806_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1807_;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_del_object(v___x_1783_);
lean_dec(v_fst_1780_);
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1849_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1790_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1790_);
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
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1786_);
lean_del_object(v___x_1783_);
lean_dec(v_fst_1780_);
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1857_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1788_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1788_);
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
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1783_);
lean_dec(v_snd_1781_);
lean_dec(v_fst_1780_);
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1865_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1785_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1785_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_dec(v_a_1775_);
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v___x_1874_ = lean_box(0);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1874_);
v___x_1876_ = v___x_1777_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
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
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1879_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1774_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1774_);
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
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1887_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1772_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1772_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1895_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1770_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1770_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1904_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1760_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1760_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_b_1738_);
lean_dec_ref(v_a_1737_);
v_a_1913_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1750_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1750_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Homo_processNewDiseq___boxed(lean_object* v_a_1921_, lean_object* v_b_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Meta_Grind_Homo_processNewDiseq(v_a_1921_, v_b_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec(v_a_1923_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_apply_11(v___y_1936_, v___y_1935_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, lean_box(0));
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec_ref(v___y_1951_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(uint8_t v___x_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_box(v___x_1963_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v___x_1027__boxed_1989_; lean_object* v_res_1990_; 
v___x_1027__boxed_1989_ = lean_unbox(v___x_1977_);
v_res_1990_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_1027__boxed_1989_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec(v___y_1978_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(lean_object* v___x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1991_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v___x_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___lam__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(v___x_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec(v___y_2005_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___f_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; 
v___f_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2028_ = l_Lean_Meta_Grind_Homo_homExt;
v___x_2029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___f_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_));
v___x_2034_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_2028_, v___x_2029_, v___x_2030_, v___x_2031_, v___f_2032_, v___f_2027_, v___f_2032_, v___f_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2____boxed(lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Lean_Meta_Tactic_Grind_Homomorphism_0__Lean_Meta_Grind_Homo_initFn_00___x40_Lean_Meta_Tactic_Grind_Homomorphism_3099954765____hygCtx___hyg_2_();
return v_res_2036_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
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
