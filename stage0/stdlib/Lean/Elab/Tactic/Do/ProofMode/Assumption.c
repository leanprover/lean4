// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Assumption
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.Exact import Lean.Meta.Tactic.Assumption
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__3_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 60, 94, 227, 159, 215, 186, 21)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Assumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 213, 83, 90, 143, 246, 89, 5)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value),LEAN_SCALAR_PTR_LITERAL(91, 95, 126, 25, 101, 250, 102, 154)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 213, 83, 90, 143, 246, 89, 5)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 136, 121, 156, 1, 251, 233)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Elab.Tactic.Do.ProofMode.Assumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Elab.Tactic.Do.ProofMode.MGoal.assumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assumption: hypothesis without proper metadata: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tautological"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 116, 221, 240, 227, 37, 93, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "PropAsSPredTautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 191, 216, 96, 0, 209, 179, 40)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Exact"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "from_tautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 90, 235, 148, 72, 45, 123, 55)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 82, 124, 192, 70, 8, 53, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "hypothesis not found"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "massumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 248, 144, 74, 231, 227, 47, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabMAssumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(63, 2, 101, 198, 46, 159, 29, 206)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___boxed(lean_object*);
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(lean_object* v_msg_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_toApplicative_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_44_; 
v___x_10_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0);
v___x_11_ = l_ReaderT_instMonad___redArg(v___x_10_);
v_toApplicative_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v___x_11_, 1);
lean_dec(v_unused_45_);
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_44_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_toApplicative_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_44_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v_toFunctor_16_; lean_object* v_toSeq_17_; lean_object* v_toSeqLeft_18_; lean_object* v_toSeqRight_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_42_; 
v_toFunctor_16_ = lean_ctor_get(v_toApplicative_12_, 0);
v_toSeq_17_ = lean_ctor_get(v_toApplicative_12_, 2);
v_toSeqLeft_18_ = lean_ctor_get(v_toApplicative_12_, 3);
v_toSeqRight_19_ = lean_ctor_get(v_toApplicative_12_, 4);
v_isSharedCheck_42_ = !lean_is_exclusive(v_toApplicative_12_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v_toApplicative_12_, 1);
lean_dec(v_unused_43_);
v___x_21_ = v_toApplicative_12_;
v_isShared_22_ = v_isSharedCheck_42_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_toSeqRight_19_);
lean_inc(v_toSeqLeft_18_);
lean_inc(v_toSeq_17_);
lean_inc(v_toFunctor_16_);
lean_dec(v_toApplicative_12_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_42_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_32_; 
v___f_23_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__1));
v___f_24_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__2));
lean_inc_ref(v_toFunctor_16_);
v___f_25_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_25_, 0, v_toFunctor_16_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_26_, 0, v_toFunctor_16_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___f_25_);
lean_ctor_set(v___x_27_, 1, v___f_26_);
v___f_28_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_28_, 0, v_toSeqRight_19_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_29_, 0, v_toSeqLeft_18_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_30_, 0, v_toSeq_17_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 4, v___f_28_);
lean_ctor_set(v___x_21_, 3, v___f_29_);
lean_ctor_set(v___x_21_, 2, v___f_30_);
lean_ctor_set(v___x_21_, 1, v___f_23_);
lean_ctor_set(v___x_21_, 0, v___x_27_);
v___x_32_ = v___x_21_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___f_23_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v___f_30_);
lean_ctor_set(v_reuseFailAlloc_41_, 3, v___f_29_);
lean_ctor_set(v_reuseFailAlloc_41_, 4, v___f_28_);
v___x_32_ = v_reuseFailAlloc_41_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_34_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v___f_24_);
lean_ctor_set(v___x_14_, 0, v___x_32_);
v___x_34_ = v___x_14_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___f_24_);
v___x_34_ = v_reuseFailAlloc_40_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_3675__overap_38_; lean_object* v___x_39_; 
v___x_35_ = l_ReaderT_instMonad___redArg(v___x_34_);
v___x_36_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, v___x_35_);
v___x_37_ = l_OptionT_instInhabitedOfPure___redArg(v___x_36_);
v___x_3675__overap_38_ = lean_panic_fn(v___x_37_, v_msg_4_);
v___x_39_ = lean_apply_5(v___x_3675__overap_38_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
return v___x_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___boxed(lean_object* v_msg_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(v_msg_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(lean_object* v_goal_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_u_91_; lean_object* v_00_u03c3s_92_; lean_object* v_hyps_93_; lean_object* v_target_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_219_; 
v_u_91_ = lean_ctor_get(v_goal_85_, 0);
v_00_u03c3s_92_ = lean_ctor_get(v_goal_85_, 1);
v_hyps_93_ = lean_ctor_get(v_goal_85_, 2);
v_target_94_ = lean_ctor_get(v_goal_85_, 3);
v_isSharedCheck_219_ = !lean_is_exclusive(v_goal_85_);
if (v_isSharedCheck_219_ == 0)
{
v___x_96_ = v_goal_85_;
v_isShared_97_ = v_isSharedCheck_219_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_target_94_);
lean_inc(v_hyps_93_);
lean_inc(v_00_u03c3s_92_);
lean_inc(v_u_91_);
lean_dec(v_goal_85_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_219_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; 
lean_inc_ref(v_hyps_93_);
v___x_98_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_hyps_93_);
if (lean_obj_tag(v___x_98_) == 1)
{
lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
lean_del_object(v___x_96_);
lean_dec_ref(v_target_94_);
lean_dec_ref(v_hyps_93_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_98_, 0);
lean_dec(v_unused_107_);
v___x_100_ = v___x_98_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_dec(v___x_98_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_box(0);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 0);
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v___x_108_; 
lean_dec(v___x_98_);
lean_inc_ref(v_hyps_93_);
v___x_108_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_hyps_93_);
if (lean_obj_tag(v___x_108_) == 1)
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_144_; 
lean_del_object(v___x_96_);
lean_dec_ref(v_hyps_93_);
v_val_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_144_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_144_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_144_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_p_113_; lean_object* v___x_114_; 
v_p_113_ = lean_ctor_get(v_val_109_, 2);
lean_inc_ref(v_p_113_);
lean_dec(v_val_109_);
lean_inc_ref(v_p_113_);
v___x_114_ = l_Lean_Meta_isExprDefEq(v_p_113_, v_target_94_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_135_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_135_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_135_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_135_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = lean_unbox(v_a_115_);
lean_dec(v_a_115_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_122_; 
lean_dec_ref(v_p_113_);
lean_del_object(v___x_111_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
v___x_120_ = lean_box(0);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_120_);
v___x_122_ = v___x_117_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__5));
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v_u_91_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = l_Lean_mkConst(v___x_124_, v___x_126_);
v___x_128_ = l_Lean_mkAppB(v___x_127_, v_00_u03c3s_92_, v_p_113_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_128_);
v___x_130_ = v___x_111_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_130_);
v___x_132_ = v___x_117_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v_p_113_);
lean_del_object(v___x_111_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
v_a_136_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_114_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_114_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v___x_108_);
v___x_145_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_93_);
if (lean_obj_tag(v___x_145_) == 1)
{
lean_object* v_val_146_; lean_object* v_snd_147_; lean_object* v_snd_148_; lean_object* v_fst_149_; lean_object* v_fst_150_; lean_object* v_fst_151_; lean_object* v_snd_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_hyps_93_);
v_val_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_146_);
lean_dec_ref(v___x_145_);
v_snd_147_ = lean_ctor_get(v_val_146_, 1);
lean_inc(v_snd_147_);
v_snd_148_ = lean_ctor_get(v_snd_147_, 1);
lean_inc(v_snd_148_);
v_fst_149_ = lean_ctor_get(v_val_146_, 0);
lean_inc(v_fst_149_);
lean_dec(v_val_146_);
v_fst_150_ = lean_ctor_get(v_snd_147_, 0);
lean_inc(v_fst_150_);
lean_dec(v_snd_147_);
v_fst_151_ = lean_ctor_get(v_snd_148_, 0);
v_snd_152_ = lean_ctor_get(v_snd_148_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_snd_148_);
if (v_isSharedCheck_209_ == 0)
{
v___x_154_ = v_snd_148_;
v_isShared_155_ = v_isSharedCheck_209_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_snd_152_);
lean_inc(v_fst_151_);
lean_dec(v_snd_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_209_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 1);
lean_ctor_set(v___x_154_, 1, v___x_156_);
lean_ctor_set(v___x_154_, 0, v_fst_149_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_fst_149_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_208_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___y_160_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_inc_ref(v_target_94_);
lean_inc(v_snd_152_);
lean_inc_ref(v_00_u03c3s_92_);
lean_inc(v_u_91_);
v___x_186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_186_, 0, v_u_91_);
lean_ctor_set(v___x_186_, 1, v_00_u03c3s_92_);
lean_ctor_set(v___x_186_, 2, v_snd_152_);
lean_ctor_set(v___x_186_, 3, v_target_94_);
lean_inc(v_a_89_);
lean_inc_ref(v_a_88_);
lean_inc(v_a_87_);
lean_inc_ref(v_a_86_);
v___x_187_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v___x_186_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
if (lean_obj_tag(v_a_188_) == 0)
{
v___y_160_ = v___x_187_;
goto v___jp_159_;
}
else
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_96_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_187_, 0);
lean_dec(v_unused_207_);
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_206_;
goto v_resetjp_189_;
}
else
{
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_206_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_205_; 
v_val_192_ = lean_ctor_get(v_a_188_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_a_188_);
if (v_isSharedCheck_205_ == 0)
{
v___x_194_ = v_a_188_;
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v_a_188_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11));
v___x_197_ = l_Lean_mkConst(v___x_196_, v___x_158_);
v___x_198_ = l_Lean_mkApp5(v___x_197_, v_fst_150_, v_fst_151_, v_snd_152_, v_target_94_, v_val_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_198_);
v___x_200_ = v___x_194_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_200_);
v___x_202_ = v___x_190_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
else
{
v___y_160_ = v___x_187_;
goto v___jp_159_;
}
v___jp_159_:
{
if (lean_obj_tag(v___y_160_) == 0)
{
lean_object* v_a_161_; 
v_a_161_ = lean_ctor_get(v___y_160_, 0);
if (lean_obj_tag(v_a_161_) == 0)
{
lean_object* v___x_163_; 
lean_dec_ref(v___y_160_);
lean_inc_ref(v_target_94_);
lean_inc(v_fst_151_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 2, v_fst_151_);
v___x_163_ = v___x_96_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_u_91_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_00_u03c3s_92_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_fst_151_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_target_94_);
v___x_163_ = v_reuseFailAlloc_185_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v___x_163_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
if (lean_obj_tag(v_a_165_) == 0)
{
lean_dec_ref(v___x_158_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_dec_ref(v_target_94_);
return v___x_164_;
}
else
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_183_; 
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_164_, 0);
lean_dec(v_unused_184_);
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_183_;
goto v_resetjp_166_;
}
else
{
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_183_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_val_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_182_; 
v_val_169_ = lean_ctor_get(v_a_165_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_a_165_);
if (v_isSharedCheck_182_ == 0)
{
v___x_171_ = v_a_165_;
v_isShared_172_ = v_isSharedCheck_182_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_val_169_);
lean_dec(v_a_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_182_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9));
v___x_174_ = l_Lean_mkConst(v___x_173_, v___x_158_);
v___x_175_ = l_Lean_mkApp5(v___x_174_, v_fst_150_, v_fst_151_, v_snd_152_, v_target_94_, v_val_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_175_);
v___x_177_ = v___x_171_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_177_);
v___x_179_ = v___x_167_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_158_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_dec_ref(v_target_94_);
return v___x_164_;
}
}
}
else
{
lean_dec_ref(v___x_158_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_del_object(v___x_96_);
lean_dec_ref(v_target_94_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
return v___y_160_;
}
}
else
{
lean_dec_ref(v___x_158_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_del_object(v___x_96_);
lean_dec_ref(v_target_94_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
return v___y_160_;
}
}
}
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v___x_145_);
lean_del_object(v___x_96_);
lean_dec_ref(v_target_94_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12));
v___x_211_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13));
v___x_212_ = lean_unsigned_to_nat(30u);
v___x_213_ = lean_unsigned_to_nat(4u);
v___x_214_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14));
v___x_215_ = lean_expr_dbg_to_string(v_hyps_93_);
lean_dec_ref(v_hyps_93_);
v___x_216_ = lean_string_append(v___x_214_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = l_mkPanicMessageWithDecl(v___x_210_, v___x_211_, v___x_212_, v___x_213_, v___x_216_);
lean_dec_ref(v___x_216_);
v___x_218_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(v___x_217_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___boxed(lean_object* v_goal_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(lean_object* v_goal_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_u_256_; lean_object* v_00_u03c3s_257_; lean_object* v_hyps_258_; lean_object* v_target_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_00_u03c6_264_; lean_object* v___x_265_; 
v_u_256_ = lean_ctor_get(v_goal_250_, 0);
lean_inc(v_u_256_);
v_00_u03c3s_257_ = lean_ctor_get(v_goal_250_, 1);
lean_inc_ref(v_00_u03c3s_257_);
v_hyps_258_ = lean_ctor_get(v_goal_250_, 2);
lean_inc_ref(v_hyps_258_);
v_target_259_ = lean_ctor_get(v_goal_250_, 3);
lean_inc_ref(v_target_259_);
lean_dec_ref(v_goal_250_);
v___x_260_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1));
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_u_256_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc_ref(v___x_262_);
v___x_263_ = l_Lean_mkConst(v___x_260_, v___x_262_);
lean_inc_ref(v_target_259_);
lean_inc_ref(v_00_u03c3s_257_);
v_00_u03c6_264_ = l_Lean_mkAppB(v___x_263_, v_00_u03c3s_257_, v_target_259_);
lean_inc(v_a_254_);
lean_inc_ref(v_a_253_);
lean_inc(v_a_252_);
lean_inc_ref(v_a_251_);
lean_inc_ref(v_00_u03c6_264_);
v___x_265_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_00_u03c6_264_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_301_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_301_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_301_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_301_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
if (lean_obj_tag(v_a_266_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec_ref(v_00_u03c6_264_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_target_259_);
lean_dec_ref(v_hyps_258_);
lean_dec_ref(v_00_u03c3s_257_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
v___x_270_ = lean_box(0);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
else
{
lean_object* v_val_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_del_object(v___x_268_);
v_val_274_ = lean_ctor_get(v_a_266_, 0);
lean_inc(v_val_274_);
lean_dec_ref(v_a_266_);
v___x_275_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3));
lean_inc_ref(v___x_262_);
v___x_276_ = l_Lean_mkConst(v___x_275_, v___x_262_);
lean_inc_ref(v_target_259_);
lean_inc_ref(v_00_u03c3s_257_);
lean_inc_ref(v_00_u03c6_264_);
v___x_277_ = l_Lean_mkApp3(v___x_276_, v_00_u03c6_264_, v_00_u03c3s_257_, v_target_259_);
v___x_278_ = lean_box(0);
v___x_279_ = l_Lean_Meta_synthInstance_x3f(v___x_277_, v___x_278_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
if (lean_obj_tag(v_a_280_) == 0)
{
lean_dec(v_val_274_);
lean_dec_ref(v_00_u03c6_264_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_target_259_);
lean_dec_ref(v_hyps_258_);
lean_dec_ref(v_00_u03c3s_257_);
return v___x_279_;
}
else
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_299_; 
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v___x_279_, 0);
lean_dec(v_unused_300_);
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_299_;
goto v_resetjp_281_;
}
else
{
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_299_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_val_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_298_; 
v_val_284_ = lean_ctor_get(v_a_280_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_280_);
if (v_isSharedCheck_298_ == 0)
{
v___x_286_ = v_a_280_;
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_val_284_);
lean_dec(v_a_280_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_288_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6));
v___x_289_ = l_Lean_mkConst(v___x_288_, v___x_262_);
v___x_290_ = l_Lean_Expr_fvar___override(v_val_274_);
v___x_291_ = l_Lean_mkApp6(v___x_289_, v_00_u03c3s_257_, v_00_u03c6_264_, v_hyps_258_, v_target_259_, v_val_284_, v___x_290_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_291_);
v___x_293_ = v___x_286_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_293_);
v___x_295_ = v___x_282_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
else
{
lean_dec(v_val_274_);
lean_dec_ref(v_00_u03c6_264_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_target_259_);
lean_dec_ref(v_hyps_258_);
lean_dec_ref(v_00_u03c3s_257_);
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_00_u03c6_264_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_target_259_);
lean_dec_ref(v_hyps_258_);
lean_dec_ref(v_00_u03c3s_257_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
v_a_302_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_265_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_265_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___boxed(lean_object* v_goal_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(v_goal_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(lean_object* v_e_317_, lean_object* v___y_318_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_Expr_hasMVar(v_e_317_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_e_317_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v_mctx_323_; lean_object* v___x_324_; lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_327_; lean_object* v_cache_328_; lean_object* v_zetaDeltaFVarIds_329_; lean_object* v_postponed_330_; lean_object* v_diag_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
v___x_322_ = lean_st_ref_get(v___y_318_);
v_mctx_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_mctx_323_);
lean_dec(v___x_322_);
v___x_324_ = l_Lean_instantiateMVarsCore(v_mctx_323_, v_e_317_);
v_fst_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_fst_325_);
v_snd_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc(v_snd_326_);
lean_dec_ref(v___x_324_);
v___x_327_ = lean_st_ref_take(v___y_318_);
v_cache_328_ = lean_ctor_get(v___x_327_, 1);
v_zetaDeltaFVarIds_329_ = lean_ctor_get(v___x_327_, 2);
v_postponed_330_ = lean_ctor_get(v___x_327_, 3);
v_diag_331_ = lean_ctor_get(v___x_327_, 4);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v___x_327_, 0);
lean_dec(v_unused_341_);
v___x_333_ = v___x_327_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_diag_331_);
lean_inc(v_postponed_330_);
lean_inc(v_zetaDeltaFVarIds_329_);
lean_inc(v_cache_328_);
lean_dec(v___x_327_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_snd_326_);
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_snd_326_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_cache_328_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_zetaDeltaFVarIds_329_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_postponed_330_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v_diag_331_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_st_ref_set(v___y_318_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_fst_325_);
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg___boxed(lean_object* v_e_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_e_342_, v___y_343_);
lean_dec(v___y_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(lean_object* v_e_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_e_346_, v___y_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___boxed(lean_object* v_e_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(v_e_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(lean_object* v_x_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = lean_apply_9(v_x_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, lean_box(0));
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed(lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(lean_object* v_mvarId_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___f_401_; lean_object* v___x_402_; 
v___f_401_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_401_, 0, v_x_391_);
lean_closure_set(v___f_401_, 1, v___y_392_);
lean_closure_set(v___f_401_, 2, v___y_393_);
lean_closure_set(v___f_401_, 3, v___y_394_);
lean_closure_set(v___f_401_, 4, v___y_395_);
v___x_402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_390_, v___f_401_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_402_) == 0)
{
return v___x_402_;
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___boxed(lean_object* v_mvarId_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(lean_object* v_00_u03b1_423_, lean_object* v_mvarId_424_, lean_object* v_x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_424_, v_x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___boxed(lean_object* v_00_u03b1_436_, lean_object* v_mvarId_437_, lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(v_00_u03b1_436_, v_mvarId_437_, v_x_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(lean_object* v_msgData_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; lean_object* v_env_456_; lean_object* v___x_457_; lean_object* v_mctx_458_; lean_object* v_lctx_459_; lean_object* v_options_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_455_ = lean_st_ref_get(v___y_453_);
v_env_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc_ref(v_env_456_);
lean_dec(v___x_455_);
v___x_457_ = lean_st_ref_get(v___y_451_);
v_mctx_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_mctx_458_);
lean_dec(v___x_457_);
v_lctx_459_ = lean_ctor_get(v___y_450_, 2);
v_options_460_ = lean_ctor_get(v___y_452_, 2);
lean_inc_ref(v_options_460_);
lean_inc_ref(v_lctx_459_);
v___x_461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_461_, 0, v_env_456_);
lean_ctor_set(v___x_461_, 1, v_mctx_458_);
lean_ctor_set(v___x_461_, 2, v_lctx_459_);
lean_ctor_set(v___x_461_, 3, v_options_460_);
v___x_462_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_msgData_449_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2___boxed(lean_object* v_msgData_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(v_msgData_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_ref_477_; lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_ref_477_ = lean_ctor_get(v___y_474_, 5);
v___x_478_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_inc(v_ref_477_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_ref_477_);
lean_ctor_set(v___x_483_, 1, v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 1);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg___boxed(lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
lean_object* v_ks_499_; lean_object* v_vs_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_524_; 
v_ks_499_ = lean_ctor_get(v_x_495_, 0);
v_vs_500_ = lean_ctor_get(v_x_495_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_524_ == 0)
{
v___x_502_ = v_x_495_;
v_isShared_503_ = v_isSharedCheck_524_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_vs_500_);
lean_inc(v_ks_499_);
lean_dec(v_x_495_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_524_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_array_get_size(v_ks_499_);
v___x_505_ = lean_nat_dec_lt(v_x_496_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec(v_x_496_);
v___x_506_ = lean_array_push(v_ks_499_, v_x_497_);
v___x_507_ = lean_array_push(v_vs_500_, v_x_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_507_);
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_509_ = v___x_502_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v_k_x27_511_; uint8_t v___x_512_; 
v_k_x27_511_ = lean_array_fget_borrowed(v_ks_499_, v_x_496_);
v___x_512_ = l_Lean_instBEqMVarId_beq(v_x_497_, v_k_x27_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; 
if (v_isShared_503_ == 0)
{
v___x_514_ = v___x_502_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_ks_499_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_vs_500_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_x_496_, v___x_515_);
lean_dec(v_x_496_);
v_x_495_ = v___x_514_;
v_x_496_ = v___x_516_;
goto _start;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_array_fset(v_ks_499_, v_x_496_, v_x_497_);
v___x_520_ = lean_array_fset(v_vs_500_, v_x_496_, v_x_498_);
lean_dec(v_x_496_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_520_);
lean_ctor_set(v___x_502_, 0, v___x_519_);
v___x_522_ = v___x_502_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(lean_object* v_n_525_, lean_object* v_k_526_, lean_object* v_v_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_n_525_, v___x_528_, v_k_526_, v_v_527_);
return v___x_529_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; 
v___x_530_ = ((size_t)5ULL);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_shift_left(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; 
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_535_ = lean_usize_sub(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(lean_object* v_x_537_, size_t v_x_538_, size_t v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v_es_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; size_t v___x_546_; lean_object* v_j_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_es_542_ = lean_ctor_get(v_x_537_, 0);
v___x_543_ = ((size_t)5ULL);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_546_ = lean_usize_land(v_x_538_, v___x_545_);
v_j_547_ = lean_usize_to_nat(v___x_546_);
v___x_548_ = lean_array_get_size(v_es_542_);
v___x_549_ = lean_nat_dec_lt(v_j_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v_j_547_);
lean_dec(v_x_541_);
lean_dec(v_x_540_);
return v_x_537_;
}
else
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_586_; 
lean_inc_ref(v_es_542_);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_x_537_, 0);
lean_dec(v_unused_587_);
v___x_551_ = v_x_537_;
v_isShared_552_ = v_isSharedCheck_586_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_x_537_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_586_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_v_553_; lean_object* v___x_554_; lean_object* v_xs_x27_555_; lean_object* v___y_557_; 
v_v_553_ = lean_array_fget(v_es_542_, v_j_547_);
v___x_554_ = lean_box(0);
v_xs_x27_555_ = lean_array_fset(v_es_542_, v_j_547_, v___x_554_);
switch(lean_obj_tag(v_v_553_))
{
case 0:
{
lean_object* v_key_562_; lean_object* v_val_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_key_562_ = lean_ctor_get(v_v_553_, 0);
v_val_563_ = lean_ctor_get(v_v_553_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_v_553_);
if (v_isSharedCheck_573_ == 0)
{
v___x_565_ = v_v_553_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_val_563_);
lean_inc(v_key_562_);
lean_dec(v_v_553_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_instBEqMVarId_beq(v_x_540_, v_key_562_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_del_object(v___x_565_);
v___x_568_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_562_, v_val_563_, v_x_540_, v_x_541_);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
v___y_557_ = v___x_569_;
goto v___jp_556_;
}
else
{
lean_object* v___x_571_; 
lean_dec(v_val_563_);
lean_dec(v_key_562_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_x_541_);
lean_ctor_set(v___x_565_, 0, v_x_540_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_x_540_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_x_541_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v___y_557_ = v___x_571_;
goto v___jp_556_;
}
}
}
}
case 1:
{
lean_object* v_node_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_584_; 
v_node_574_ = lean_ctor_get(v_v_553_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_v_553_);
if (v_isSharedCheck_584_ == 0)
{
v___x_576_ = v_v_553_;
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_node_574_);
lean_dec(v_v_553_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_578_ = lean_usize_shift_right(v_x_538_, v___x_543_);
v___x_579_ = lean_usize_add(v_x_539_, v___x_544_);
v___x_580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_node_574_, v___x_578_, v___x_579_, v_x_540_, v_x_541_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_580_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v___y_557_ = v___x_582_;
goto v___jp_556_;
}
}
}
default: 
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_x_540_);
lean_ctor_set(v___x_585_, 1, v_x_541_);
v___y_557_ = v___x_585_;
goto v___jp_556_;
}
}
v___jp_556_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_array_fset(v_xs_x27_555_, v_j_547_, v___y_557_);
lean_dec(v_j_547_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_558_);
v___x_560_ = v___x_551_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
else
{
lean_object* v_ks_588_; lean_object* v_vs_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_609_; 
v_ks_588_ = lean_ctor_get(v_x_537_, 0);
v_vs_589_ = lean_ctor_get(v_x_537_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_609_ == 0)
{
v___x_591_ = v_x_537_;
v_isShared_592_ = v_isSharedCheck_609_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_vs_589_);
lean_inc(v_ks_588_);
lean_dec(v_x_537_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_609_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_ks_588_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_vs_589_);
v___x_594_ = v_reuseFailAlloc_608_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v_newNode_595_; uint8_t v___y_597_; size_t v___x_603_; uint8_t v___x_604_; 
v_newNode_595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v___x_594_, v_x_540_, v_x_541_);
v___x_603_ = ((size_t)7ULL);
v___x_604_ = lean_usize_dec_le(v___x_603_, v_x_539_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_595_);
v___x_606_ = lean_unsigned_to_nat(4u);
v___x_607_ = lean_nat_dec_lt(v___x_605_, v___x_606_);
lean_dec(v___x_605_);
v___y_597_ = v___x_607_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___x_604_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
lean_object* v_ks_598_; lean_object* v_vs_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_ks_598_ = lean_ctor_get(v_newNode_595_, 0);
lean_inc_ref(v_ks_598_);
v_vs_599_ = lean_ctor_get(v_newNode_595_, 1);
lean_inc_ref(v_vs_599_);
lean_dec_ref(v_newNode_595_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_x_539_, v_ks_598_, v_vs_599_, v___x_600_, v___x_601_);
lean_dec_ref(v_vs_599_);
lean_dec_ref(v_ks_598_);
return v___x_602_;
}
else
{
return v_newNode_595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(size_t v_depth_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_i_613_, lean_object* v_entries_614_){
_start:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_array_get_size(v_keys_611_);
v___x_616_ = lean_nat_dec_lt(v_i_613_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec(v_i_613_);
return v_entries_614_;
}
else
{
lean_object* v_k_617_; lean_object* v_v_618_; uint64_t v___x_619_; size_t v_h_620_; size_t v___x_621_; lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v_h_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_k_617_ = lean_array_fget_borrowed(v_keys_611_, v_i_613_);
v_v_618_ = lean_array_fget_borrowed(v_vals_612_, v_i_613_);
v___x_619_ = l_Lean_instHashableMVarId_hash(v_k_617_);
v_h_620_ = lean_uint64_to_usize(v___x_619_);
v___x_621_ = ((size_t)5ULL);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_sub(v_depth_610_, v___x_623_);
v___x_625_ = lean_usize_mul(v___x_621_, v___x_624_);
v_h_626_ = lean_usize_shift_right(v_h_620_, v___x_625_);
v___x_627_ = lean_nat_add(v_i_613_, v___x_622_);
lean_dec(v_i_613_);
lean_inc(v_v_618_);
lean_inc(v_k_617_);
v___x_628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_entries_614_, v_h_626_, v_depth_610_, v_k_617_, v_v_618_);
v_i_613_ = v___x_627_;
v_entries_614_ = v___x_628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_depth_630_, lean_object* v_keys_631_, lean_object* v_vals_632_, lean_object* v_i_633_, lean_object* v_entries_634_){
_start:
{
size_t v_depth_boxed_635_; lean_object* v_res_636_; 
v_depth_boxed_635_ = lean_unbox_usize(v_depth_630_);
lean_dec(v_depth_630_);
v_res_636_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_boxed_635_, v_keys_631_, v_vals_632_, v_i_633_, v_entries_634_);
lean_dec_ref(v_vals_632_);
lean_dec_ref(v_keys_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
size_t v_x_6369__boxed_642_; size_t v_x_6370__boxed_643_; lean_object* v_res_644_; 
v_x_6369__boxed_642_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_x_6370__boxed_643_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_637_, v_x_6369__boxed_642_, v_x_6370__boxed_643_, v_x_640_, v_x_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
uint64_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_648_ = l_Lean_instHashableMVarId_hash(v_x_646_);
v___x_649_ = lean_uint64_to_usize(v___x_648_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_645_, v___x_649_, v___x_650_, v_x_646_, v_x_647_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(lean_object* v_mvarId_652_, lean_object* v_val_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v_mctx_657_; lean_object* v_cache_658_; lean_object* v_zetaDeltaFVarIds_659_; lean_object* v_postponed_660_; lean_object* v_diag_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_688_; 
v___x_656_ = lean_st_ref_take(v___y_654_);
v_mctx_657_ = lean_ctor_get(v___x_656_, 0);
v_cache_658_ = lean_ctor_get(v___x_656_, 1);
v_zetaDeltaFVarIds_659_ = lean_ctor_get(v___x_656_, 2);
v_postponed_660_ = lean_ctor_get(v___x_656_, 3);
v_diag_661_ = lean_ctor_get(v___x_656_, 4);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_688_ == 0)
{
v___x_663_ = v___x_656_;
v_isShared_664_ = v_isSharedCheck_688_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_diag_661_);
lean_inc(v_postponed_660_);
lean_inc(v_zetaDeltaFVarIds_659_);
lean_inc(v_cache_658_);
lean_inc(v_mctx_657_);
lean_dec(v___x_656_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_688_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_depth_665_; lean_object* v_levelAssignDepth_666_; lean_object* v_mvarCounter_667_; lean_object* v_lDepth_668_; lean_object* v_decls_669_; lean_object* v_userNames_670_; lean_object* v_lAssignment_671_; lean_object* v_eAssignment_672_; lean_object* v_dAssignment_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_687_; 
v_depth_665_ = lean_ctor_get(v_mctx_657_, 0);
v_levelAssignDepth_666_ = lean_ctor_get(v_mctx_657_, 1);
v_mvarCounter_667_ = lean_ctor_get(v_mctx_657_, 2);
v_lDepth_668_ = lean_ctor_get(v_mctx_657_, 3);
v_decls_669_ = lean_ctor_get(v_mctx_657_, 4);
v_userNames_670_ = lean_ctor_get(v_mctx_657_, 5);
v_lAssignment_671_ = lean_ctor_get(v_mctx_657_, 6);
v_eAssignment_672_ = lean_ctor_get(v_mctx_657_, 7);
v_dAssignment_673_ = lean_ctor_get(v_mctx_657_, 8);
v_isSharedCheck_687_ = !lean_is_exclusive(v_mctx_657_);
if (v_isSharedCheck_687_ == 0)
{
v___x_675_ = v_mctx_657_;
v_isShared_676_ = v_isSharedCheck_687_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_dAssignment_673_);
lean_inc(v_eAssignment_672_);
lean_inc(v_lAssignment_671_);
lean_inc(v_userNames_670_);
lean_inc(v_decls_669_);
lean_inc(v_lDepth_668_);
lean_inc(v_mvarCounter_667_);
lean_inc(v_levelAssignDepth_666_);
lean_inc(v_depth_665_);
lean_dec(v_mctx_657_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_687_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_eAssignment_672_, v_mvarId_652_, v_val_653_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 7, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_depth_665_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_levelAssignDepth_666_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_mvarCounter_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_lDepth_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_decls_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_userNames_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_lAssignment_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_dAssignment_673_);
v___x_679_ = v_reuseFailAlloc_686_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_679_);
v___x_681_ = v___x_663_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_cache_658_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_zetaDeltaFVarIds_659_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_postponed_660_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_diag_661_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_st_ref_set(v___y_654_, v___x_681_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg___boxed(lean_object* v_mvarId_689_, lean_object* v_val_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_689_, v_val_690_, v___y_691_);
lean_dec(v___y_691_);
return v_res_693_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(lean_object* v_a_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___y_711_; lean_object* v___x_727_; 
lean_inc(v_a_700_);
v___x_727_ = l_Lean_MVarId_getType(v_a_700_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_a_728_, v___y_706_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_730_);
lean_dec(v_a_730_);
if (lean_obj_tag(v___x_731_) == 1)
{
lean_object* v_val_732_; lean_object* v___x_733_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_732_);
lean_dec_ref(v___x_731_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v_val_732_);
v___x_733_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_val_732_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
if (lean_obj_tag(v_a_734_) == 0)
{
lean_object* v___x_735_; 
lean_dec_ref(v___x_733_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
v___x_735_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(v_val_732_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
v___y_711_ = v___x_735_;
goto v___jp_710_;
}
else
{
lean_dec_ref(v_a_734_);
lean_dec(v_val_732_);
v___y_711_ = v___x_733_;
goto v___jp_710_;
}
}
else
{
lean_dec(v_val_732_);
v___y_711_ = v___x_733_;
goto v___jp_710_;
}
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v___x_731_);
lean_dec(v_a_700_);
v___x_736_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3);
v___x_737_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v___x_736_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v___x_737_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v_a_700_);
v_a_738_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_727_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_727_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
v___jp_710_:
{
if (lean_obj_tag(v___y_711_) == 0)
{
lean_object* v_a_712_; 
v_a_712_ = lean_ctor_get(v___y_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___y_711_);
if (lean_obj_tag(v_a_712_) == 1)
{
lean_object* v_val_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_val_713_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v_a_712_);
v___x_714_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_a_700_, v_val_713_, v___y_706_);
lean_dec_ref(v___x_714_);
v___x_715_ = lean_box(0);
v___x_716_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_715_, v___y_702_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_a_712_);
lean_dec(v_a_700_);
v___x_717_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1);
v___x_718_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v___x_717_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
return v___x_718_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v_a_700_);
v_a_719_ = lean_ctor_get(v___y_711_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___y_711_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___y_711_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___y_711_);
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
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed(lean_object* v_a_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(v_a_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_758_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___f_768_; lean_object* v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
lean_inc(v_a_767_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_768_, 0, v_a_767_);
v___x_769_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_a_767_, v___f_768_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
return v___x_769_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
v_a_770_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_766_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___boxed(lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(lean_object* v_x_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed(lean_object* v_x_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(v_x_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_x_799_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(lean_object* v_mvarId_810_, lean_object* v_val_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_810_, v_val_811_, v___y_817_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___boxed(lean_object* v_mvarId_822_, lean_object* v_val_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(v_mvarId_822_, v_val_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(lean_object* v_00_u03b1_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_msg_835_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___boxed(lean_object* v_00_u03b1_846_, lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(v_00_u03b1_846_, v_msg_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_x_859_, v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, size_t v_x_865_, size_t v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_864_, v_x_865_, v_x_866_, v_x_867_, v_x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_6863__boxed_876_; size_t v_x_6864__boxed_877_; lean_object* v_res_878_; 
v_x_6863__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_6864__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(v_00_u03b2_870_, v_x_871_, v_x_6863__boxed_876_, v_x_6864__boxed_877_, v_x_874_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_879_, lean_object* v_n_880_, lean_object* v_k_881_, lean_object* v_v_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v_n_880_, v_k_881_, v_v_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_884_, size_t v_depth_885_, lean_object* v_keys_886_, lean_object* v_vals_887_, lean_object* v_heq_888_, lean_object* v_i_889_, lean_object* v_entries_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_885_, v_keys_886_, v_vals_887_, v_i_889_, v_entries_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b2_892_, lean_object* v_depth_893_, lean_object* v_keys_894_, lean_object* v_vals_895_, lean_object* v_heq_896_, lean_object* v_i_897_, lean_object* v_entries_898_){
_start:
{
size_t v_depth_boxed_899_; lean_object* v_res_900_; 
v_depth_boxed_899_ = lean_unbox_usize(v_depth_893_);
lean_dec(v_depth_893_);
v_res_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(v_00_u03b2_892_, v_depth_boxed_899_, v_keys_894_, v_vals_895_, v_heq_896_, v_i_897_, v_entries_898_);
lean_dec_ref(v_vals_895_);
lean_dec_ref(v_keys_894_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_x_902_, v_x_903_, v_x_904_, v_x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1(){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_926_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3));
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7));
v___x_929_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed), 10, 0);
v___x_930_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_926_, v___x_927_, v___x_928_, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___boxed(lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
return v_res_932_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
}
#ifdef __cplusplus
}
#endif
