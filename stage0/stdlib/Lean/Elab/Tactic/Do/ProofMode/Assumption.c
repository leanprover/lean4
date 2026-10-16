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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 213, 83, 90, 143, 246, 89, 5)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__8_value),LEAN_SCALAR_PTR_LITERAL(173, 214, 136, 121, 156, 1, 251, 233)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__6_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 213, 83, 90, 143, 246, 89, 5)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 95, 126, 25, 101, 250, 102, 154)}};
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_instMonadEIO___redArg();
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
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_3276__overap_38_; lean_object* v___x_39_; 
v___x_35_ = l_StateRefT_x27_instMonad___redArg(v___x_34_);
v___x_36_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, v___x_35_);
v___x_37_ = l_OptionT_instInhabitedOfPure___redArg(v___x_36_);
v___x_3276__overap_38_ = lean_panic_fn_borrowed(v___x_37_, v_msg_4_);
lean_dec(v___x_37_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
v___x_39_ = lean_apply_5(v___x_3276__overap_38_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
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
lean_object* v_u_91_; lean_object* v_00_u03c3s_92_; lean_object* v_hyps_93_; lean_object* v_target_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_215_; 
v_u_91_ = lean_ctor_get(v_goal_85_, 0);
v_00_u03c3s_92_ = lean_ctor_get(v_goal_85_, 1);
v_hyps_93_ = lean_ctor_get(v_goal_85_, 2);
v_target_94_ = lean_ctor_get(v_goal_85_, 3);
v_isSharedCheck_215_ = !lean_is_exclusive(v_goal_85_);
if (v_isSharedCheck_215_ == 0)
{
v___x_96_ = v_goal_85_;
v_isShared_97_ = v_isSharedCheck_215_;
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
v_isShared_97_ = v_isSharedCheck_215_;
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
lean_object* v_val_146_; lean_object* v_snd_147_; lean_object* v_snd_148_; lean_object* v_fst_149_; lean_object* v_fst_150_; lean_object* v_fst_151_; lean_object* v_snd_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_205_; 
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
v_isSharedCheck_205_ = !lean_is_exclusive(v_snd_148_);
if (v_isSharedCheck_205_ == 0)
{
v___x_154_ = v_snd_148_;
v_isShared_155_ = v_isSharedCheck_205_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_snd_152_);
lean_inc(v_fst_151_);
lean_dec(v_snd_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_205_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_156_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__9));
v___x_157_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 1);
lean_ctor_set(v___x_154_, 1, v___x_157_);
lean_ctor_set(v___x_154_, 0, v_fst_149_);
v___x_159_ = v___x_154_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_fst_149_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_204_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc_ref(v___x_159_);
v___x_160_ = l_Lean_mkConst(v___x_156_, v___x_159_);
lean_inc_ref(v_target_94_);
lean_inc(v_snd_152_);
lean_inc_ref(v_00_u03c3s_92_);
lean_inc(v_u_91_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 2, v_snd_152_);
v___x_162_ = v___x_96_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_u_91_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_00_u03c3s_92_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_snd_152_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_target_94_);
v___x_162_ = v_reuseFailAlloc_203_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v___x_162_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_202_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_202_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_202_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_202_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
if (lean_obj_tag(v_a_164_) == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_del_object(v___x_166_);
lean_dec_ref(v___x_160_);
v___x_168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__11));
v___x_169_ = l_Lean_mkConst(v___x_168_, v___x_159_);
lean_inc_ref(v_target_94_);
lean_inc(v_fst_151_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_u_91_);
lean_ctor_set(v___x_170_, 1, v_00_u03c3s_92_);
lean_ctor_set(v___x_170_, 2, v_fst_151_);
lean_ctor_set(v___x_170_, 3, v_target_94_);
v___x_171_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v___x_170_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
if (lean_obj_tag(v_a_172_) == 0)
{
lean_dec_ref(v___x_169_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_dec_ref(v_target_94_);
return v___x_171_;
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_188_; 
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v___x_171_, 0);
lean_dec(v_unused_189_);
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_188_;
goto v_resetjp_173_;
}
else
{
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_188_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_val_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_187_; 
v_val_176_ = lean_ctor_get(v_a_172_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_172_);
if (v_isSharedCheck_187_ == 0)
{
v___x_178_ = v_a_172_;
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_val_176_);
lean_dec(v_a_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = l_Lean_mkApp5(v___x_169_, v_fst_150_, v_fst_151_, v_snd_152_, v_target_94_, v_val_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_186_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_182_);
v___x_184_ = v___x_174_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_169_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_dec_ref(v_target_94_);
return v___x_171_;
}
}
else
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v___x_159_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
v_val_190_ = lean_ctor_get(v_a_164_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_a_164_);
if (v_isSharedCheck_201_ == 0)
{
v___x_192_ = v_a_164_;
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v_a_164_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_mkApp5(v___x_160_, v_fst_150_, v_fst_151_, v_snd_152_, v_target_94_, v_val_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_196_);
v___x_198_ = v___x_166_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_160_);
lean_dec_ref(v___x_159_);
lean_dec(v_snd_152_);
lean_dec(v_fst_151_);
lean_dec(v_fst_150_);
lean_dec_ref(v_target_94_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
return v___x_163_;
}
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v___x_145_);
lean_del_object(v___x_96_);
lean_dec_ref(v_target_94_);
lean_dec_ref(v_00_u03c3s_92_);
lean_dec(v_u_91_);
v___x_206_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__12));
v___x_207_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__13));
v___x_208_ = lean_unsigned_to_nat(30u);
v___x_209_ = lean_unsigned_to_nat(4u);
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___closed__14));
v___x_211_ = lean_expr_dbg_to_string(v_hyps_93_);
lean_dec_ref(v_hyps_93_);
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
lean_dec_ref(v___x_211_);
v___x_213_ = l_mkPanicMessageWithDecl(v___x_206_, v___x_207_, v___x_208_, v___x_209_, v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption_spec__0(v___x_213_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption___boxed(lean_object* v_goal_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(lean_object* v_goal_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_u_252_; lean_object* v_00_u03c3s_253_; lean_object* v_hyps_254_; lean_object* v_target_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_00_u03c6_260_; lean_object* v___x_261_; 
v_u_252_ = lean_ctor_get(v_goal_246_, 0);
lean_inc(v_u_252_);
v_00_u03c3s_253_ = lean_ctor_get(v_goal_246_, 1);
lean_inc_ref_n(v_00_u03c3s_253_, 2);
v_hyps_254_ = lean_ctor_get(v_goal_246_, 2);
lean_inc_ref(v_hyps_254_);
v_target_255_ = lean_ctor_get(v_goal_246_, 3);
lean_inc_ref_n(v_target_255_, 2);
lean_dec_ref(v_goal_246_);
v___x_256_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__1));
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v_u_252_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
lean_inc_ref(v___x_258_);
v___x_259_ = l_Lean_mkConst(v___x_256_, v___x_258_);
v_00_u03c6_260_ = l_Lean_mkAppB(v___x_259_, v_00_u03c3s_253_, v_target_255_);
lean_inc_ref(v_00_u03c6_260_);
v___x_261_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_00_u03c6_260_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_297_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_297_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_297_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_297_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
if (lean_obj_tag(v_a_262_) == 0)
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_dec_ref(v_00_u03c6_260_);
lean_dec_ref_known(v___x_258_, 2);
lean_dec_ref(v_target_255_);
lean_dec_ref(v_hyps_254_);
lean_dec_ref(v_00_u03c3s_253_);
v___x_266_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
lean_object* v_val_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_del_object(v___x_264_);
v_val_270_ = lean_ctor_get(v_a_262_, 0);
lean_inc(v_val_270_);
lean_dec_ref_known(v_a_262_, 1);
v___x_271_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__3));
lean_inc_ref(v___x_258_);
v___x_272_ = l_Lean_mkConst(v___x_271_, v___x_258_);
lean_inc_ref(v_target_255_);
lean_inc_ref(v_00_u03c3s_253_);
lean_inc_ref(v_00_u03c6_260_);
v___x_273_ = l_Lean_mkApp3(v___x_272_, v_00_u03c6_260_, v_00_u03c3s_253_, v_target_255_);
v___x_274_ = lean_box(0);
v___x_275_ = l_Lean_Meta_synthInstance_x3f(v___x_273_, v___x_274_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
if (lean_obj_tag(v_a_276_) == 0)
{
lean_dec(v_val_270_);
lean_dec_ref(v_00_u03c6_260_);
lean_dec_ref_known(v___x_258_, 2);
lean_dec_ref(v_target_255_);
lean_dec_ref(v_hyps_254_);
lean_dec_ref(v_00_u03c3s_253_);
return v___x_275_;
}
else
{
lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_295_; 
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v___x_275_, 0);
lean_dec(v_unused_296_);
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_295_;
goto v_resetjp_277_;
}
else
{
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_295_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_val_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_294_; 
v_val_280_ = lean_ctor_get(v_a_276_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_a_276_);
if (v_isSharedCheck_294_ == 0)
{
v___x_282_ = v_a_276_;
v_isShared_283_ = v_isSharedCheck_294_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_val_280_);
lean_dec(v_a_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_294_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_284_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___closed__6));
v___x_285_ = l_Lean_mkConst(v___x_284_, v___x_258_);
v___x_286_ = l_Lean_Expr_fvar___override(v_val_270_);
v___x_287_ = l_Lean_mkApp6(v___x_285_, v_00_u03c3s_253_, v_00_u03c6_260_, v_hyps_254_, v_target_255_, v_val_280_, v___x_286_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_287_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_293_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_291_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_289_);
v___x_291_ = v___x_278_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
else
{
lean_dec(v_val_270_);
lean_dec_ref(v_00_u03c6_260_);
lean_dec_ref_known(v___x_258_, 2);
lean_dec_ref(v_target_255_);
lean_dec_ref(v_hyps_254_);
lean_dec_ref(v_00_u03c3s_253_);
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_00_u03c6_260_);
lean_dec_ref_known(v___x_258_, 2);
lean_dec_ref(v_target_255_);
lean_dec_ref(v_hyps_254_);
lean_dec_ref(v_00_u03c3s_253_);
v_a_298_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_261_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_261_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure___boxed(lean_object* v_goal_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(v_goal_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(lean_object* v_e_313_, lean_object* v___y_314_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = l_Lean_Expr_hasMVar(v_e_313_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_e_313_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v_mctx_319_; lean_object* v___x_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; lean_object* v___x_323_; lean_object* v_cache_324_; lean_object* v_zetaDeltaFVarIds_325_; lean_object* v_postponed_326_; lean_object* v_diag_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_336_; 
v___x_318_ = lean_st_ref_get(v___y_314_);
v_mctx_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc_ref(v_mctx_319_);
lean_dec(v___x_318_);
v___x_320_ = l_Lean_instantiateMVarsCore(v_mctx_319_, v_e_313_);
v_fst_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_fst_321_);
v_snd_322_ = lean_ctor_get(v___x_320_, 1);
lean_inc(v_snd_322_);
lean_dec_ref(v___x_320_);
v___x_323_ = lean_st_ref_take(v___y_314_);
v_cache_324_ = lean_ctor_get(v___x_323_, 1);
v_zetaDeltaFVarIds_325_ = lean_ctor_get(v___x_323_, 2);
v_postponed_326_ = lean_ctor_get(v___x_323_, 3);
v_diag_327_ = lean_ctor_get(v___x_323_, 4);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v___x_323_, 0);
lean_dec(v_unused_337_);
v___x_329_ = v___x_323_;
v_isShared_330_ = v_isSharedCheck_336_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_diag_327_);
lean_inc(v_postponed_326_);
lean_inc(v_zetaDeltaFVarIds_325_);
lean_inc(v_cache_324_);
lean_dec(v___x_323_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_336_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_snd_322_);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_snd_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_cache_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_zetaDeltaFVarIds_325_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_postponed_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_diag_327_);
v___x_332_ = v_reuseFailAlloc_335_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_st_ref_put(v___y_314_, v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_fst_321_);
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg___boxed(lean_object* v_e_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_e_338_, v___y_339_);
lean_dec(v___y_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(lean_object* v_e_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_e_342_, v___y_348_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___boxed(lean_object* v_e_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1(v_e_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
v___x_374_ = lean_apply_9(v_x_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, lean_box(0));
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed(lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0(v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(lean_object* v_mvarId_386_, lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; 
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_397_, 0, v_x_387_);
lean_closure_set(v___f_397_, 1, v___y_388_);
lean_closure_set(v___f_397_, 2, v___y_389_);
lean_closure_set(v___f_397_, 3, v___y_390_);
lean_closure_set(v___f_397_, 4, v___y_391_);
v___x_398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_386_, v___f_397_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_398_) == 0)
{
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg___boxed(lean_object* v_mvarId_407_, lean_object* v_x_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_407_, v_x_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(lean_object* v_00_u03b1_419_, lean_object* v_mvarId_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_mvarId_420_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___boxed(lean_object* v_00_u03b1_432_, lean_object* v_mvarId_433_, lean_object* v_x_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3(v_00_u03b1_432_, v_mvarId_433_, v_x_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_ks_449_; lean_object* v_vs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_474_; 
v_ks_449_ = lean_ctor_get(v_x_445_, 0);
v_vs_450_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_474_ == 0)
{
v___x_452_ = v_x_445_;
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_vs_450_);
lean_inc(v_ks_449_);
lean_dec(v_x_445_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_array_get_size(v_ks_449_);
v___x_455_ = lean_nat_dec_lt(v_x_446_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_x_446_);
v___x_456_ = lean_array_push(v_ks_449_, v_x_447_);
v___x_457_ = lean_array_push(v_vs_450_, v_x_448_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_457_);
lean_ctor_set(v___x_452_, 0, v___x_456_);
v___x_459_ = v___x_452_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
lean_object* v_k_x27_461_; uint8_t v___x_462_; 
v_k_x27_461_ = lean_array_fget_borrowed(v_ks_449_, v_x_446_);
v___x_462_ = l_Lean_instBEqMVarId_beq(v_x_447_, v_k_x27_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; 
if (v_isShared_453_ == 0)
{
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ks_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_vs_450_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_x_446_, v___x_465_);
lean_dec(v_x_446_);
v_x_445_ = v___x_464_;
v_x_446_ = v___x_466_;
goto _start;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_array_fset(v_ks_449_, v_x_446_, v_x_447_);
v___x_470_ = lean_array_fset(v_vs_450_, v_x_446_, v_x_448_);
lean_dec(v_x_446_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_470_);
lean_ctor_set(v___x_452_, 0, v___x_469_);
v___x_472_ = v___x_452_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(lean_object* v_n_475_, lean_object* v_k_476_, lean_object* v_v_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_n_475_, v___x_478_, v_k_476_, v_v_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_es_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v_j_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_es_486_ = lean_ctor_get(v_x_481_, 0);
v___x_487_ = ((size_t)31ULL);
v___x_488_ = lean_usize_land(v_x_482_, v___x_487_);
v_j_489_ = lean_usize_to_nat(v___x_488_);
v___x_490_ = lean_array_get_size(v_es_486_);
v___x_491_ = lean_nat_dec_lt(v_j_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec(v_j_489_);
lean_dec(v_x_485_);
lean_dec(v_x_484_);
return v_x_481_;
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_530_; 
lean_inc_ref(v_es_486_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_x_481_, 0);
lean_dec(v_unused_531_);
v___x_493_ = v_x_481_;
v_isShared_494_ = v_isSharedCheck_530_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_x_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_530_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_v_495_; lean_object* v___x_496_; lean_object* v_xs_x27_497_; lean_object* v___y_499_; 
v_v_495_ = lean_array_fget(v_es_486_, v_j_489_);
v___x_496_ = lean_box(0);
v_xs_x27_497_ = lean_array_fset(v_es_486_, v_j_489_, v___x_496_);
switch(lean_obj_tag(v_v_495_))
{
case 0:
{
lean_object* v_key_504_; lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_key_504_ = lean_ctor_get(v_v_495_, 0);
v_val_505_ = lean_ctor_get(v_v_495_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_v_495_);
if (v_isSharedCheck_515_ == 0)
{
v___x_507_ = v_v_495_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_inc(v_key_504_);
lean_dec(v_v_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; 
v___x_509_ = l_Lean_instBEqMVarId_beq(v_x_484_, v_key_504_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_del_object(v___x_507_);
v___x_510_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_504_, v_val_505_, v_x_484_, v_x_485_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
v___y_499_ = v___x_511_;
goto v___jp_498_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_val_505_);
lean_dec(v_key_504_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v_x_485_);
lean_ctor_set(v___x_507_, 0, v_x_484_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_x_484_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_x_485_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v___y_499_ = v___x_513_;
goto v___jp_498_;
}
}
}
}
case 1:
{
lean_object* v_node_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_528_; 
v_node_516_ = lean_ctor_get(v_v_495_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_v_495_);
if (v_isSharedCheck_528_ == 0)
{
v___x_518_ = v_v_495_;
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_node_516_);
lean_dec(v_v_495_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_520_ = ((size_t)5ULL);
v___x_521_ = lean_usize_shift_right(v_x_482_, v___x_520_);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_x_483_, v___x_522_);
v___x_524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_node_516_, v___x_521_, v___x_523_, v_x_484_, v_x_485_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_524_);
v___x_526_ = v___x_518_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_499_ = v___x_526_;
goto v___jp_498_;
}
}
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_x_484_);
lean_ctor_set(v___x_529_, 1, v_x_485_);
v___y_499_ = v___x_529_;
goto v___jp_498_;
}
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_array_fset(v_xs_x27_497_, v_j_489_, v___y_499_);
lean_dec(v_j_489_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_500_);
v___x_502_ = v___x_493_;
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
}
else
{
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_551_; 
v_ks_532_ = lean_ctor_get(v_x_481_, 0);
v_vs_533_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_551_ == 0)
{
v___x_535_ = v_x_481_;
v_isShared_536_ = v_isSharedCheck_551_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_481_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_551_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_vs_533_);
v___x_538_ = v_reuseFailAlloc_550_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v_newNode_539_; size_t v___x_540_; uint8_t v___x_541_; 
v_newNode_539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v___x_538_, v_x_484_, v_x_485_);
v___x_540_ = ((size_t)7ULL);
v___x_541_ = lean_usize_dec_le(v___x_540_, v_x_483_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_539_);
v___x_543_ = lean_unsigned_to_nat(4u);
v___x_544_ = lean_nat_dec_lt(v___x_542_, v___x_543_);
lean_dec(v___x_542_);
if (v___x_544_ == 0)
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_ks_545_ = lean_ctor_get(v_newNode_539_, 0);
lean_inc_ref(v_ks_545_);
v_vs_546_ = lean_ctor_get(v_newNode_539_, 1);
lean_inc_ref(v_vs_546_);
lean_dec_ref(v_newNode_539_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_x_483_, v_ks_545_, v_vs_546_, v___x_547_, v___x_548_);
lean_dec_ref(v_vs_546_);
lean_dec_ref(v_ks_545_);
return v___x_549_;
}
else
{
return v_newNode_539_;
}
}
else
{
return v_newNode_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(size_t v_depth_552_, lean_object* v_keys_553_, lean_object* v_vals_554_, lean_object* v_i_555_, lean_object* v_entries_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_keys_553_);
v___x_558_ = lean_nat_dec_lt(v_i_555_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_i_555_);
return v_entries_556_;
}
else
{
lean_object* v_k_559_; lean_object* v_v_560_; uint64_t v___x_561_; size_t v_h_562_; size_t v___x_563_; lean_object* v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v_h_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_k_559_ = lean_array_fget_borrowed(v_keys_553_, v_i_555_);
v_v_560_ = lean_array_fget_borrowed(v_vals_554_, v_i_555_);
v___x_561_ = l_Lean_instHashableMVarId_hash(v_k_559_);
v_h_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = ((size_t)5ULL);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_sub(v_depth_552_, v___x_565_);
v___x_567_ = lean_usize_mul(v___x_563_, v___x_566_);
v_h_568_ = lean_usize_shift_right(v_h_562_, v___x_567_);
v___x_569_ = lean_nat_add(v_i_555_, v___x_564_);
lean_dec(v_i_555_);
lean_inc(v_v_560_);
lean_inc(v_k_559_);
v___x_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_entries_556_, v_h_568_, v_depth_552_, v_k_559_, v_v_560_);
v_i_555_ = v___x_569_;
v_entries_556_ = v___x_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_depth_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_i_575_, lean_object* v_entries_576_){
_start:
{
size_t v_depth_boxed_577_; lean_object* v_res_578_; 
v_depth_boxed_577_ = lean_unbox_usize(v_depth_572_);
lean_dec(v_depth_572_);
v_res_578_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_boxed_577_, v_keys_573_, v_vals_574_, v_i_575_, v_entries_576_);
lean_dec_ref(v_vals_574_);
lean_dec_ref(v_keys_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_6326__boxed_584_; size_t v_x_6327__boxed_585_; lean_object* v_res_586_; 
v_x_6326__boxed_584_ = lean_unbox_usize(v_x_580_);
lean_dec(v_x_580_);
v_x_6327__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_res_586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_579_, v_x_6326__boxed_584_, v_x_6327__boxed_585_, v_x_582_, v_x_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
uint64_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_590_ = l_Lean_instHashableMVarId_hash(v_x_588_);
v___x_591_ = lean_uint64_to_usize(v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_587_, v___x_591_, v___x_592_, v_x_588_, v_x_589_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(lean_object* v_mvarId_594_, lean_object* v_val_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_mctx_599_; lean_object* v_cache_600_; lean_object* v_zetaDeltaFVarIds_601_; lean_object* v_postponed_602_; lean_object* v_diag_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_633_; 
v___x_598_ = lean_st_ref_take(v___y_596_);
v_mctx_599_ = lean_ctor_get(v___x_598_, 0);
v_cache_600_ = lean_ctor_get(v___x_598_, 1);
v_zetaDeltaFVarIds_601_ = lean_ctor_get(v___x_598_, 2);
v_postponed_602_ = lean_ctor_get(v___x_598_, 3);
v_diag_603_ = lean_ctor_get(v___x_598_, 4);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_633_ == 0)
{
v___x_605_ = v___x_598_;
v_isShared_606_ = v_isSharedCheck_633_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_diag_603_);
lean_inc(v_postponed_602_);
lean_inc(v_zetaDeltaFVarIds_601_);
lean_inc(v_cache_600_);
lean_inc(v_mctx_599_);
lean_dec(v___x_598_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_633_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_depth_607_; lean_object* v_levelAssignDepth_608_; lean_object* v_lmvarCounter_609_; lean_object* v_mvarCounter_610_; lean_object* v_lDecls_611_; lean_object* v_decls_612_; lean_object* v_userNames_613_; lean_object* v_lAssignment_614_; lean_object* v_eAssignment_615_; lean_object* v_dAssignment_616_; lean_object* v_instanceTypedMVars_617_; lean_object* v_synthNormMemo_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
v_depth_607_ = lean_ctor_get(v_mctx_599_, 0);
v_levelAssignDepth_608_ = lean_ctor_get(v_mctx_599_, 1);
v_lmvarCounter_609_ = lean_ctor_get(v_mctx_599_, 2);
v_mvarCounter_610_ = lean_ctor_get(v_mctx_599_, 3);
v_lDecls_611_ = lean_ctor_get(v_mctx_599_, 4);
v_decls_612_ = lean_ctor_get(v_mctx_599_, 5);
v_userNames_613_ = lean_ctor_get(v_mctx_599_, 6);
v_lAssignment_614_ = lean_ctor_get(v_mctx_599_, 7);
v_eAssignment_615_ = lean_ctor_get(v_mctx_599_, 8);
v_dAssignment_616_ = lean_ctor_get(v_mctx_599_, 9);
v_instanceTypedMVars_617_ = lean_ctor_get(v_mctx_599_, 10);
v_synthNormMemo_618_ = lean_ctor_get(v_mctx_599_, 11);
v_isSharedCheck_632_ = !lean_is_exclusive(v_mctx_599_);
if (v_isSharedCheck_632_ == 0)
{
v___x_620_ = v_mctx_599_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_synthNormMemo_618_);
lean_inc(v_instanceTypedMVars_617_);
lean_inc(v_dAssignment_616_);
lean_inc(v_eAssignment_615_);
lean_inc(v_lAssignment_614_);
lean_inc(v_userNames_613_);
lean_inc(v_decls_612_);
lean_inc(v_lDecls_611_);
lean_inc(v_mvarCounter_610_);
lean_inc(v_lmvarCounter_609_);
lean_inc(v_levelAssignDepth_608_);
lean_inc(v_depth_607_);
lean_dec(v_mctx_599_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_622_ = lean_box(0);
v___x_623_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_eAssignment_615_, v_mvarId_594_, v_val_595_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 8, v___x_623_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_depth_607_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_levelAssignDepth_608_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_lmvarCounter_609_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_mvarCounter_610_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_lDecls_611_);
lean_ctor_set(v_reuseFailAlloc_631_, 5, v_decls_612_);
lean_ctor_set(v_reuseFailAlloc_631_, 6, v_userNames_613_);
lean_ctor_set(v_reuseFailAlloc_631_, 7, v_lAssignment_614_);
lean_ctor_set(v_reuseFailAlloc_631_, 8, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_631_, 9, v_dAssignment_616_);
lean_ctor_set(v_reuseFailAlloc_631_, 10, v_instanceTypedMVars_617_);
lean_ctor_set(v_reuseFailAlloc_631_, 11, v_synthNormMemo_618_);
v___x_625_ = v_reuseFailAlloc_631_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_625_);
v___x_627_ = v___x_605_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_cache_600_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_zetaDeltaFVarIds_601_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_postponed_602_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v_diag_603_);
v___x_627_ = v_reuseFailAlloc_630_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_st_ref_put(v___y_596_, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_622_);
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg___boxed(lean_object* v_mvarId_634_, lean_object* v_val_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_634_, v_val_635_, v___y_636_);
lean_dec(v___y_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2_spec__3(lean_object* v_msgData_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; uint8_t v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; lean_object* v_toCold_650_; lean_object* v_mctx_651_; lean_object* v_lctx_652_; lean_object* v_options_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_645_ = lean_st_ref_get(v___y_643_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
v___x_647_ = 0;
v_env_648_ = l_Lean_Environment_setRecordingDeps(v_env_646_, v___x_647_);
v___x_649_ = lean_st_ref_get(v___y_641_);
v_toCold_650_ = lean_ctor_get(v___y_642_, 0);
v_mctx_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_mctx_651_);
lean_dec(v___x_649_);
v_lctx_652_ = lean_ctor_get(v___y_640_, 2);
v_options_653_ = lean_ctor_get(v_toCold_650_, 2);
lean_inc_ref(v_options_653_);
lean_inc_ref(v_lctx_652_);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_648_);
lean_ctor_set(v___x_654_, 1, v_mctx_651_);
lean_ctor_set(v___x_654_, 2, v_lctx_652_);
lean_ctor_set(v___x_654_, 3, v_options_653_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_msgData_639_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2_spec__3___boxed(lean_object* v_msgData_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2_spec__3(v_msgData_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_ref_670_; lean_object* v___x_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_ref_670_ = lean_ctor_get(v___y_667_, 2);
v___x_671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2_spec__3(v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc(v_ref_670_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_ref_670_);
lean_ctor_set(v___x_676_, 1, v_a_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 1);
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg___boxed(lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_msg_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__0));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__2));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(lean_object* v_a_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_val_705_; lean_object* v___x_709_; 
lean_inc(v_a_694_);
v___x_709_ = l_Lean_MVarId_getType(v_a_694_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__1___redArg(v_a_710_, v___y_700_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_712_);
lean_dec(v_a_712_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_n(v_val_714_, 2);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_val_714_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
if (lean_obj_tag(v_a_716_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumptionPure(v_val_714_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
if (lean_obj_tag(v_a_718_) == 1)
{
lean_object* v_val_719_; 
v_val_719_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v_a_718_, 1);
v_val_705_ = v_val_719_;
goto v___jp_704_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_a_718_);
lean_dec(v_a_694_);
v___x_720_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__1);
v___x_721_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v___x_720_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_721_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_694_);
v_a_722_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_717_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_717_);
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
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_val_730_; 
lean_dec(v_val_714_);
v_val_730_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_a_716_, 1);
v_val_705_ = v_val_730_;
goto v___jp_704_;
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_val_714_);
lean_dec(v_a_694_);
v_a_731_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_715_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_715_);
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
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v___x_713_);
lean_dec(v_a_694_);
v___x_739_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___closed__3);
v___x_740_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v___x_739_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_740_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_694_);
v_a_741_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_709_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_709_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_a_694_, v_val_705_, v___y_700_);
lean_dec_ref(v___x_706_);
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_707_, v___y_696_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed(lean_object* v_a_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0(v_a_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_761_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___f_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_771_, 0, v_a_770_);
v___x_772_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__3___redArg(v_a_770_, v___f_771_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_772_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_773_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_769_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg___boxed(lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(lean_object* v_x_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___redArg(v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed(lean_object* v_x_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption(v_x_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_x_802_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(lean_object* v_mvarId_813_, lean_object* v_val_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___redArg(v_mvarId_813_, v_val_814_, v___y_820_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0___boxed(lean_object* v_mvarId_825_, lean_object* v_val_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0(v_mvarId_825_, v_val_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(lean_object* v_00_u03b1_837_, lean_object* v_msg_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___redArg(v_msg_838_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2___boxed(lean_object* v_00_u03b1_849_, lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__2(v_00_u03b1_849_, v_msg_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0___redArg(v_x_862_, v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, size_t v_x_868_, size_t v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___redArg(v_x_867_, v_x_868_, v_x_869_, v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
size_t v_x_6841__boxed_879_; size_t v_x_6842__boxed_880_; lean_object* v_res_881_; 
v_x_6841__boxed_879_ = lean_unbox_usize(v_x_875_);
lean_dec(v_x_875_);
v_x_6842__boxed_880_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_res_881_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3(v_00_u03b2_873_, v_x_874_, v_x_6841__boxed_879_, v_x_6842__boxed_880_, v_x_877_, v_x_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_882_, lean_object* v_n_883_, lean_object* v_k_884_, lean_object* v_v_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6___redArg(v_n_883_, v_k_884_, v_v_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_887_, size_t v_depth_888_, lean_object* v_keys_889_, lean_object* v_vals_890_, lean_object* v_heq_891_, lean_object* v_i_892_, lean_object* v_entries_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___redArg(v_depth_888_, v_keys_889_, v_vals_890_, v_i_892_, v_entries_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_00_u03b2_895_, lean_object* v_depth_896_, lean_object* v_keys_897_, lean_object* v_vals_898_, lean_object* v_heq_899_, lean_object* v_i_900_, lean_object* v_entries_901_){
_start:
{
size_t v_depth_boxed_902_; lean_object* v_res_903_; 
v_depth_boxed_902_ = lean_unbox_usize(v_depth_896_);
lean_dec(v_depth_896_);
v_res_903_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__7(v_00_u03b2_895_, v_depth_boxed_902_, v_keys_897_, v_vals_898_, v_heq_899_, v_i_900_, v_entries_901_);
lean_dec_ref(v_vals_898_);
lean_dec_ref(v_keys_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMAssumption_spec__0_spec__0_spec__3_spec__6_spec__7___redArg(v_x_905_, v_x_906_, v_x_907_, v_x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1(){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__3));
v___x_931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___closed__7));
v___x_932_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___boxed), 10, 0);
v___x_933_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_929_, v___x_930_, v___x_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1___boxed(lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Assumption_0__Lean_Elab_Tactic_Do_ProofMode_elabMAssumption___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMAssumption__1();
return v_res_935_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
