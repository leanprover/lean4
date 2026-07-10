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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "massumption"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(115, 248, 144, 74, 231, 227, 47, 25)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabMAssumption"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(63, 2, 101, 198, 46, 159, 29, 206)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___boxed(lean_object*);
static lean_object* _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(lean_object* v_msg_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v_toApplicative_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_44_; 
v___x_10_ = lean_obj_once(&l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0, &l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0___closed__0);
v___x_11_ = l_StateRefT_x27_instMonad___redArg(v___x_10_);
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
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_3557__overap_38_; lean_object* v___x_39_; 
v___x_35_ = l_StateRefT_x27_instMonad___redArg(v___x_34_);
v___x_36_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, v___x_35_);
v___x_37_ = l_OptionT_instInhabitedOfPure___redArg(v___x_36_);
v___x_3557__overap_38_ = lean_panic_fn_borrowed(v___x_37_, v_msg_4_);
lean_dec(v___x_37_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
v___x_39_ = lean_apply_5(v___x_3557__overap_38_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
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
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
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
lean_inc_ref_n(v_p_113_, 2);
lean_dec(v_val_109_);
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
lean_dec_ref_known(v___x_145_, 1);
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
lean_dec_ref_known(v___y_160_, 1);
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
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
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
lean_inc_ref_n(v_00_u03c3s_257_, 2);
v_hyps_258_ = lean_ctor_get(v_goal_250_, 2);
lean_inc_ref(v_hyps_258_);
v_target_259_ = lean_ctor_get(v_goal_250_, 3);
lean_inc_ref_n(v_target_259_, 2);
lean_dec_ref(v_goal_250_);
v___x_260_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1));
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_u_256_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc_ref(v___x_262_);
v___x_263_ = l_Lean_mkConst(v___x_260_, v___x_262_);
v_00_u03c6_264_ = l_Lean_mkAppB(v___x_263_, v_00_u03c3s_257_, v_target_259_);
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
lean_dec_ref_known(v___x_262_, 2);
lean_dec_ref(v_target_259_);
lean_dec_ref(v_hyps_258_);
lean_dec_ref(v_00_u03c3s_257_);
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
lean_dec_ref_known(v_a_266_, 1);
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
lean_dec_ref_known(v___x_262_, 2);
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
lean_dec_ref_known(v___x_262_, 2);
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
lean_dec_ref_known(v___x_262_, 2);
lean_dec_ref(v_target_259_);
lean_dec_ref(v_hyps_258_);
lean_dec_ref(v_00_u03c3s_257_);
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
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(lean_object* v_e_317_, lean_object* v___y_318_){
_start:
{
uint8_t v___x_320_; uint8_t v___x_321_; 
v___x_320_ = l_Lean_Expr_hasMVar(v_e_317_);
v___x_321_ = lean_bool_not(v___x_320_);
if (v___x_321_ == 0)
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
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v_e_317_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg___boxed(lean_object* v_e_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_e_343_, v___y_344_);
lean_dec(v___y_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(lean_object* v_e_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_e_347_, v___y_353_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___boxed(lean_object* v_e_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(v_e_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(lean_object* v_x_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
v___x_379_ = lean_apply_9(v_x_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, lean_box(0));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed(lean_object* v_x_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(v_x_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(lean_object* v_mvarId_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___f_402_; lean_object* v___x_403_; 
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
lean_inc(v___y_394_);
lean_inc_ref(v___y_393_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_402_, 0, v_x_392_);
lean_closure_set(v___f_402_, 1, v___y_393_);
lean_closure_set(v___f_402_, 2, v___y_394_);
lean_closure_set(v___f_402_, 3, v___y_395_);
lean_closure_set(v___f_402_, 4, v___y_396_);
v___x_403_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_391_, v___f_402_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_403_) == 0)
{
return v___x_403_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___boxed(lean_object* v_mvarId_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_412_, v_x_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(lean_object* v_00_u03b1_424_, lean_object* v_mvarId_425_, lean_object* v_x_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_425_, v_x_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___boxed(lean_object* v_00_u03b1_437_, lean_object* v_mvarId_438_, lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(v_00_u03b1_437_, v_mvarId_438_, v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(lean_object* v_msgData_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; lean_object* v_env_457_; lean_object* v___x_458_; lean_object* v_mctx_459_; lean_object* v_lctx_460_; lean_object* v_options_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_456_ = lean_st_ref_get(v___y_454_);
v_env_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc_ref(v_env_457_);
lean_dec(v___x_456_);
v___x_458_ = lean_st_ref_get(v___y_452_);
v_mctx_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_mctx_459_);
lean_dec(v___x_458_);
v_lctx_460_ = lean_ctor_get(v___y_451_, 2);
v_options_461_ = lean_ctor_get(v___y_453_, 2);
lean_inc_ref(v_options_461_);
lean_inc_ref(v_lctx_460_);
v___x_462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_462_, 0, v_env_457_);
lean_ctor_set(v___x_462_, 1, v_mctx_459_);
lean_ctor_set(v___x_462_, 2, v_lctx_460_);
lean_ctor_set(v___x_462_, 3, v_options_461_);
v___x_463_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v_msgData_450_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2___boxed(lean_object* v_msgData_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(v_msgData_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_ref_478_; lean_object* v___x_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
v_ref_478_ = lean_ctor_get(v___y_475_, 5);
v___x_479_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1_spec__2(v_msg_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_inc(v_ref_478_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_ref_478_);
lean_ctor_set(v___x_484_, 1, v_a_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 1);
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg___boxed(lean_object* v_msg_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_msg_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_ks_500_; lean_object* v_vs_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_525_; 
v_ks_500_ = lean_ctor_get(v_x_496_, 0);
v_vs_501_ = lean_ctor_get(v_x_496_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_525_ == 0)
{
v___x_503_ = v_x_496_;
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_vs_501_);
lean_inc(v_ks_500_);
lean_dec(v_x_496_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_get_size(v_ks_500_);
v___x_506_ = lean_nat_dec_lt(v_x_497_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_x_497_);
v___x_507_ = lean_array_push(v_ks_500_, v_x_498_);
v___x_508_ = lean_array_push(v_vs_501_, v_x_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_508_);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_k_x27_512_; uint8_t v___x_513_; 
v_k_x27_512_ = lean_array_fget_borrowed(v_ks_500_, v_x_497_);
v___x_513_ = l_Lean_instBEqMVarId_beq(v_x_498_, v_k_x27_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_515_; 
if (v_isShared_504_ == 0)
{
v___x_515_ = v___x_503_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_ks_500_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_vs_501_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_x_497_, v___x_516_);
lean_dec(v_x_497_);
v_x_496_ = v___x_515_;
v_x_497_ = v___x_517_;
goto _start;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_array_fset(v_ks_500_, v_x_497_, v_x_498_);
v___x_521_ = lean_array_fset(v_vs_501_, v_x_497_, v_x_499_);
lean_dec(v_x_497_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_521_);
lean_ctor_set(v___x_503_, 0, v___x_520_);
v___x_523_ = v___x_503_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(lean_object* v_n_526_, lean_object* v_k_527_, lean_object* v_v_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_n_526_, v___x_529_, v_k_527_, v_v_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(lean_object* v_x_532_, size_t v_x_533_, size_t v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v_es_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v_j_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_es_537_ = lean_ctor_get(v_x_532_, 0);
v___x_538_ = ((size_t)31ULL);
v___x_539_ = lean_usize_land(v_x_533_, v___x_538_);
v_j_540_ = lean_usize_to_nat(v___x_539_);
v___x_541_ = lean_array_get_size(v_es_537_);
v___x_542_ = lean_nat_dec_lt(v_j_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_dec(v_j_540_);
lean_dec(v_x_536_);
lean_dec(v_x_535_);
return v_x_532_;
}
else
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_537_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_532_, 0);
lean_dec(v_unused_582_);
v___x_544_ = v_x_532_;
v_isShared_545_ = v_isSharedCheck_581_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_x_532_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_581_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_v_546_; lean_object* v___x_547_; lean_object* v_xs_x27_548_; lean_object* v___y_550_; 
v_v_546_ = lean_array_fget(v_es_537_, v_j_540_);
v___x_547_ = lean_box(0);
v_xs_x27_548_ = lean_array_fset(v_es_537_, v_j_540_, v___x_547_);
switch(lean_obj_tag(v_v_546_))
{
case 0:
{
lean_object* v_key_555_; lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_566_; 
v_key_555_ = lean_ctor_get(v_v_546_, 0);
v_val_556_ = lean_ctor_get(v_v_546_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_v_546_);
if (v_isSharedCheck_566_ == 0)
{
v___x_558_ = v_v_546_;
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_inc(v_key_555_);
lean_dec(v_v_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint8_t v___x_560_; 
v___x_560_ = l_Lean_instBEqMVarId_beq(v_x_535_, v_key_555_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_del_object(v___x_558_);
v___x_561_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_555_, v_val_556_, v_x_535_, v_x_536_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___y_550_ = v___x_562_;
goto v___jp_549_;
}
else
{
lean_object* v___x_564_; 
lean_dec(v_val_556_);
lean_dec(v_key_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_x_536_);
lean_ctor_set(v___x_558_, 0, v_x_535_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_x_535_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_x_536_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_550_ = v___x_564_;
goto v___jp_549_;
}
}
}
}
case 1:
{
lean_object* v_node_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
v_node_567_ = lean_ctor_get(v_v_546_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_v_546_);
if (v_isSharedCheck_579_ == 0)
{
v___x_569_ = v_v_546_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_node_567_);
lean_dec(v_v_546_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_571_ = ((size_t)5ULL);
v___x_572_ = lean_usize_shift_right(v_x_533_, v___x_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_x_534_, v___x_573_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_node_567_, v___x_572_, v___x_574_, v_x_535_, v_x_536_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_575_);
v___x_577_ = v___x_569_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v___y_550_ = v___x_577_;
goto v___jp_549_;
}
}
}
default: 
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_x_535_);
lean_ctor_set(v___x_580_, 1, v_x_536_);
v___y_550_ = v___x_580_;
goto v___jp_549_;
}
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_array_fset(v_xs_x27_548_, v_j_540_, v___y_550_);
lean_dec(v_j_540_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_551_);
v___x_553_ = v___x_544_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_ks_583_ = lean_ctor_get(v_x_532_, 0);
v_vs_584_ = lean_ctor_get(v_x_532_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v_x_532_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_vs_584_);
lean_inc(v_ks_583_);
lean_dec(v_x_532_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_ks_583_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_vs_584_);
v___x_589_ = v_reuseFailAlloc_603_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v_newNode_590_; uint8_t v___y_592_; size_t v___x_598_; uint8_t v___x_599_; 
v_newNode_590_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v___x_589_, v_x_535_, v_x_536_);
v___x_598_ = ((size_t)7ULL);
v___x_599_ = lean_usize_dec_le(v___x_598_, v_x_534_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_590_);
v___x_601_ = lean_unsigned_to_nat(4u);
v___x_602_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___y_592_ = v___x_602_;
goto v___jp_591_;
}
else
{
v___y_592_ = v___x_599_;
goto v___jp_591_;
}
v___jp_591_:
{
if (v___y_592_ == 0)
{
lean_object* v_ks_593_; lean_object* v_vs_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_ks_593_ = lean_ctor_get(v_newNode_590_, 0);
lean_inc_ref(v_ks_593_);
v_vs_594_ = lean_ctor_get(v_newNode_590_, 1);
lean_inc_ref(v_vs_594_);
lean_dec_ref(v_newNode_590_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_x_534_, v_ks_593_, v_vs_594_, v___x_595_, v___x_596_);
lean_dec_ref(v_vs_594_);
lean_dec_ref(v_ks_593_);
return v___x_597_;
}
else
{
return v_newNode_590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(size_t v_depth_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_i_608_, lean_object* v_entries_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_606_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v_entries_609_;
}
else
{
lean_object* v_k_612_; lean_object* v_v_613_; uint64_t v___x_614_; size_t v_h_615_; size_t v___x_616_; lean_object* v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v_h_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_k_612_ = lean_array_fget_borrowed(v_keys_606_, v_i_608_);
v_v_613_ = lean_array_fget_borrowed(v_vals_607_, v_i_608_);
v___x_614_ = l_Lean_instHashableMVarId_hash(v_k_612_);
v_h_615_ = lean_uint64_to_usize(v___x_614_);
v___x_616_ = ((size_t)5ULL);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v_depth_605_, v___x_618_);
v___x_620_ = lean_usize_mul(v___x_616_, v___x_619_);
v_h_621_ = lean_usize_shift_right(v_h_615_, v___x_620_);
v___x_622_ = lean_nat_add(v_i_608_, v___x_617_);
lean_dec(v_i_608_);
lean_inc(v_v_613_);
lean_inc(v_k_612_);
v___x_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_entries_609_, v_h_621_, v_depth_605_, v_k_612_, v_v_613_);
v_i_608_ = v___x_622_;
v_entries_609_ = v___x_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_depth_625_, lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
size_t v_depth_boxed_630_; lean_object* v_res_631_; 
v_depth_boxed_630_ = lean_unbox_usize(v_depth_625_);
lean_dec(v_depth_625_);
v_res_631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_boxed_630_, v_keys_626_, v_vals_627_, v_i_628_, v_entries_629_);
lean_dec_ref(v_vals_627_);
lean_dec_ref(v_keys_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
size_t v_x_6309__boxed_637_; size_t v_x_6310__boxed_638_; lean_object* v_res_639_; 
v_x_6309__boxed_637_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_x_6310__boxed_638_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_632_, v_x_6309__boxed_637_, v_x_6310__boxed_638_, v_x_635_, v_x_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint64_t v___x_643_; size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_643_ = l_Lean_instHashableMVarId_hash(v_x_641_);
v___x_644_ = lean_uint64_to_usize(v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_640_, v___x_644_, v___x_645_, v_x_641_, v_x_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(lean_object* v_mvarId_647_, lean_object* v_val_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; lean_object* v_mctx_652_; lean_object* v_cache_653_; lean_object* v_zetaDeltaFVarIds_654_; lean_object* v_postponed_655_; lean_object* v_diag_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_684_; 
v___x_651_ = lean_st_ref_take(v___y_649_);
v_mctx_652_ = lean_ctor_get(v___x_651_, 0);
v_cache_653_ = lean_ctor_get(v___x_651_, 1);
v_zetaDeltaFVarIds_654_ = lean_ctor_get(v___x_651_, 2);
v_postponed_655_ = lean_ctor_get(v___x_651_, 3);
v_diag_656_ = lean_ctor_get(v___x_651_, 4);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_684_ == 0)
{
v___x_658_ = v___x_651_;
v_isShared_659_ = v_isSharedCheck_684_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_diag_656_);
lean_inc(v_postponed_655_);
lean_inc(v_zetaDeltaFVarIds_654_);
lean_inc(v_cache_653_);
lean_inc(v_mctx_652_);
lean_dec(v___x_651_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_684_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_depth_660_; lean_object* v_levelAssignDepth_661_; lean_object* v_lmvarCounter_662_; lean_object* v_mvarCounter_663_; lean_object* v_lDecls_664_; lean_object* v_decls_665_; lean_object* v_userNames_666_; lean_object* v_lAssignment_667_; lean_object* v_eAssignment_668_; lean_object* v_dAssignment_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_683_; 
v_depth_660_ = lean_ctor_get(v_mctx_652_, 0);
v_levelAssignDepth_661_ = lean_ctor_get(v_mctx_652_, 1);
v_lmvarCounter_662_ = lean_ctor_get(v_mctx_652_, 2);
v_mvarCounter_663_ = lean_ctor_get(v_mctx_652_, 3);
v_lDecls_664_ = lean_ctor_get(v_mctx_652_, 4);
v_decls_665_ = lean_ctor_get(v_mctx_652_, 5);
v_userNames_666_ = lean_ctor_get(v_mctx_652_, 6);
v_lAssignment_667_ = lean_ctor_get(v_mctx_652_, 7);
v_eAssignment_668_ = lean_ctor_get(v_mctx_652_, 8);
v_dAssignment_669_ = lean_ctor_get(v_mctx_652_, 9);
v_isSharedCheck_683_ = !lean_is_exclusive(v_mctx_652_);
if (v_isSharedCheck_683_ == 0)
{
v___x_671_ = v_mctx_652_;
v_isShared_672_ = v_isSharedCheck_683_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_dAssignment_669_);
lean_inc(v_eAssignment_668_);
lean_inc(v_lAssignment_667_);
lean_inc(v_userNames_666_);
lean_inc(v_decls_665_);
lean_inc(v_lDecls_664_);
lean_inc(v_mvarCounter_663_);
lean_inc(v_lmvarCounter_662_);
lean_inc(v_levelAssignDepth_661_);
lean_inc(v_depth_660_);
lean_dec(v_mctx_652_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_683_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_eAssignment_668_, v_mvarId_647_, v_val_648_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 8, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_depth_660_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_levelAssignDepth_661_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_lmvarCounter_662_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_mvarCounter_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_lDecls_664_);
lean_ctor_set(v_reuseFailAlloc_682_, 5, v_decls_665_);
lean_ctor_set(v_reuseFailAlloc_682_, 6, v_userNames_666_);
lean_ctor_set(v_reuseFailAlloc_682_, 7, v_lAssignment_667_);
lean_ctor_set(v_reuseFailAlloc_682_, 8, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_682_, 9, v_dAssignment_669_);
v___x_675_ = v_reuseFailAlloc_682_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_675_);
v___x_677_ = v___x_658_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_cache_653_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_zetaDeltaFVarIds_654_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_postponed_655_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_diag_656_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_st_ref_set(v___y_649_, v___x_677_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg___boxed(lean_object* v_mvarId_685_, lean_object* v_val_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_685_, v_val_686_, v___y_687_);
lean_dec(v___y_687_);
return v_res_689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(lean_object* v_a_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___y_707_; lean_object* v___x_723_; 
lean_inc(v_a_696_);
v___x_723_ = l_Lean_MVarId_getType(v_a_696_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_a_724_, v___y_702_);
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v___x_727_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_726_);
lean_dec(v_a_726_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_n(v_val_728_, 2);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_val_728_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
if (lean_obj_tag(v_a_730_) == 0)
{
lean_object* v___x_731_; 
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(v_val_728_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v___y_707_ = v___x_731_;
goto v___jp_706_;
}
else
{
lean_dec_ref_known(v_a_730_, 1);
lean_dec(v_val_728_);
v___y_707_ = v___x_729_;
goto v___jp_706_;
}
}
else
{
lean_dec(v_val_728_);
v___y_707_ = v___x_729_;
goto v___jp_706_;
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v___x_727_);
lean_dec(v_a_696_);
v___x_732_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3);
v___x_733_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v___x_732_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_733_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_696_);
v_a_734_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_723_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_723_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
v___jp_706_:
{
if (lean_obj_tag(v___y_707_) == 0)
{
lean_object* v_a_708_; 
v_a_708_ = lean_ctor_get(v___y_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___y_707_, 1);
if (lean_obj_tag(v_a_708_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_val_709_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_a_708_, 1);
v___x_710_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_a_696_, v_val_709_, v___y_702_);
lean_dec_ref(v___x_710_);
v___x_711_ = lean_box(0);
v___x_712_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_711_, v___y_698_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_a_708_);
lean_dec(v_a_696_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1);
v___x_714_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v___x_713_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
return v___x_714_;
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_a_696_);
v_a_715_ = lean_ctor_get(v___y_707_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___y_707_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___y_707_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___y_707_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed(lean_object* v_a_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(v_a_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_754_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___f_764_; lean_object* v___x_765_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc_n(v_a_763_, 2);
lean_dec_ref_known(v___x_762_, 1);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_764_, 0, v_a_763_);
v___x_765_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_a_763_, v___f_764_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v___x_765_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_762_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_762_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___boxed(lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(lean_object* v_x_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed(lean_object* v_x_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(v_x_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_x_795_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(lean_object* v_mvarId_806_, lean_object* v_val_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_806_, v_val_807_, v___y_813_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___boxed(lean_object* v_mvarId_818_, lean_object* v_val_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(v_mvarId_818_, v_val_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(lean_object* v_00_u03b1_830_, lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_msg_831_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___boxed(lean_object* v_00_u03b1_842_, lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(v_00_u03b1_842_, v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_x_855_, v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, size_t v_x_861_, size_t v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_860_, v_x_861_, v_x_862_, v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
size_t v_x_6749__boxed_872_; size_t v_x_6750__boxed_873_; lean_object* v_res_874_; 
v_x_6749__boxed_872_ = lean_unbox_usize(v_x_868_);
lean_dec(v_x_868_);
v_x_6750__boxed_873_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_res_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(v_00_u03b2_866_, v_x_867_, v_x_6749__boxed_872_, v_x_6750__boxed_873_, v_x_870_, v_x_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_875_, lean_object* v_n_876_, lean_object* v_k_877_, lean_object* v_v_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v_n_876_, v_k_877_, v_v_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_880_, size_t v_depth_881_, lean_object* v_keys_882_, lean_object* v_vals_883_, lean_object* v_heq_884_, lean_object* v_i_885_, lean_object* v_entries_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_881_, v_keys_882_, v_vals_883_, v_i_885_, v_entries_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b2_888_, lean_object* v_depth_889_, lean_object* v_keys_890_, lean_object* v_vals_891_, lean_object* v_heq_892_, lean_object* v_i_893_, lean_object* v_entries_894_){
_start:
{
size_t v_depth_boxed_895_; lean_object* v_res_896_; 
v_depth_boxed_895_ = lean_unbox_usize(v_depth_889_);
lean_dec(v_depth_889_);
v_res_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(v_00_u03b2_888_, v_depth_boxed_895_, v_keys_890_, v_vals_891_, v_heq_892_, v_i_893_, v_entries_894_);
lean_dec_ref(v_vals_891_);
lean_dec_ref(v_keys_890_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_x_898_, v_x_899_, v_x_900_, v_x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1(){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_922_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3));
v___x_924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7));
v___x_925_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed), 10, 0);
v___x_926_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_922_, v___x_923_, v___x_924_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___boxed(lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
return v_res_928_;
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
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
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
