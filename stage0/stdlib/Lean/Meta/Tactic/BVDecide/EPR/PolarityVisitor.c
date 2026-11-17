// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor
// Imports: public import Lean.Meta.Tactic.BVDecide.EPR.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_instHashableBool___lam__0___boxed(lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__3(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__2_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__7_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__9_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__10_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__12_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: !body.hasLooseBVar 0\n      "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "_private.Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor.0.Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor.visitProp'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Tactic.BVDecide.EPR.PolarityVisitor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__4_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__8_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__10_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__12_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__0(lean_object* v_a_1_, lean_object* v_toPure_2_, lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_1_);
lean_ctor_set(v___x_4_, 1, v_s_3_);
v___x_5_ = lean_apply_2(v_toPure_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__1(lean_object* v_toPure_6_, lean_object* v_ref_7_, lean_object* v_inst_8_, lean_object* v_toBind_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_11_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_a_10_);
lean_closure_set(v___f_11_, 1, v_toPure_6_);
v___x_12_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_12_, 0, lean_box(0));
lean_closure_set(v___x_12_, 1, lean_box(0));
lean_closure_set(v___x_12_, 2, v_ref_7_);
v___x_13_ = lean_apply_2(v_inst_8_, lean_box(0), v___x_12_);
v___x_14_ = lean_apply_4(v_toBind_9_, lean_box(0), lean_box(0), v___x_13_, v___f_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__2(lean_object* v_toPure_15_, lean_object* v_inst_16_, lean_object* v_toBind_17_, lean_object* v_x_18_, lean_object* v_ref_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_inc(v_toBind_17_);
lean_inc(v_ref_19_);
v___f_20_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__1), 5, 4);
lean_closure_set(v___f_20_, 0, v_toPure_15_);
lean_closure_set(v___f_20_, 1, v_ref_19_);
lean_closure_set(v___f_20_, 2, v_inst_16_);
lean_closure_set(v___f_20_, 3, v_toBind_17_);
v___x_21_ = lean_apply_1(v_x_18_, v_ref_19_);
v___x_22_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_21_, v___f_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__3(lean_object* v_toPure_23_, lean_object* v_____x_24_){
_start:
{
lean_object* v_fst_25_; lean_object* v___x_26_; 
v_fst_25_ = lean_ctor_get(v_____x_24_, 0);
lean_inc(v_fst_25_);
lean_dec_ref(v_____x_24_);
v___x_26_ = lean_apply_2(v_toPure_23_, lean_box(0), v_fst_25_);
return v___x_26_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_unsigned_to_nat(16u);
v___x_29_ = lean_mk_array(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__0);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__1);
v___x_34_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_34_, 0, lean_box(0));
lean_closure_set(v___x_34_, 1, lean_box(0));
lean_closure_set(v___x_34_, 2, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg(lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_toApplicative_38_; lean_object* v_toBind_39_; lean_object* v_toPure_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_toApplicative_38_ = lean_ctor_get(v_inst_35_, 0);
lean_inc_ref(v_toApplicative_38_);
v_toBind_39_ = lean_ctor_get(v_inst_35_, 1);
lean_inc_n(v_toBind_39_, 3);
lean_dec_ref(v_inst_35_);
v_toPure_40_ = lean_ctor_get(v_toApplicative_38_, 1);
lean_inc_n(v_toPure_40_, 2);
lean_dec_ref(v_toApplicative_38_);
v___x_41_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2);
lean_inc(v_inst_36_);
v___x_42_ = lean_apply_2(v_inst_36_, lean_box(0), v___x_41_);
v___f_43_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__2), 5, 4);
lean_closure_set(v___f_43_, 0, v_toPure_40_);
lean_closure_set(v___f_43_, 1, v_inst_36_);
lean_closure_set(v___f_43_, 2, v_toBind_39_);
lean_closure_set(v___f_43_, 3, v_x_37_);
v___f_44_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___lam__3), 2, 1);
lean_closure_set(v___f_44_, 0, v_toPure_40_);
v___x_45_ = lean_apply_4(v_toBind_39_, lean_box(0), lean_box(0), v___x_42_, v___f_43_);
v___x_46_ = lean_apply_4(v_toBind_39_, lean_box(0), lean_box(0), v___x_45_, v___f_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run(lean_object* v_m_47_, lean_object* v_inst_48_, lean_object* v_00_u03c3_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_00_u03b1_52_, lean_object* v_x_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg(v_inst_48_, v_inst_51_, v_x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0(lean_object* v_x_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
lean_inc(v_a_56_);
v___x_58_ = lean_apply_1(v_x_55_, v_a_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0___boxed(lean_object* v_x_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0(v_x_59_, v_a_60_, v_a_61_);
lean_dec(v_a_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__1(lean_object* v___f_63_, lean_object* v___f_64_, lean_object* v___x_65_, lean_object* v_s_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_63_, v___f_64_, v_s_66_, v___x_65_, v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2(lean_object* v___x_73_, lean_object* v_e_74_, uint8_t v_polarity_75_, lean_object* v___f_76_, lean_object* v_a_77_, lean_object* v_inst_78_, lean_object* v_toBind_79_, lean_object* v___f_80_, lean_object* v_toApplicative_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___f_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__1));
v___f_84_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_84_, 0, v___x_73_);
lean_closure_set(v___f_84_, 1, v___f_83_);
v___x_85_ = lean_box(v_polarity_75_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_e_74_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
lean_inc_ref(v___x_86_);
lean_inc_ref(v___f_76_);
lean_inc_ref(v___f_84_);
v___x_87_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_84_, v___f_76_, v_a_82_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec_ref(v_toApplicative_81_);
v___f_88_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__1), 4, 3);
lean_closure_set(v___f_88_, 0, v___f_84_);
lean_closure_set(v___f_88_, 1, v___f_76_);
lean_closure_set(v___f_88_, 2, v___x_86_);
lean_inc(v_a_77_);
v___x_89_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_89_, 0, lean_box(0));
lean_closure_set(v___x_89_, 1, lean_box(0));
lean_closure_set(v___x_89_, 2, lean_box(0));
lean_closure_set(v___x_89_, 3, v_a_77_);
lean_closure_set(v___x_89_, 4, v___f_88_);
v___x_90_ = lean_apply_2(v_inst_78_, lean_box(0), v___x_89_);
v___x_91_ = lean_apply_4(v_toBind_79_, lean_box(0), lean_box(0), v___x_90_, v___f_80_);
return v___x_91_;
}
else
{
lean_object* v_toPure_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec_ref_known(v___x_86_, 2);
lean_dec_ref(v___f_84_);
lean_dec(v___f_80_);
lean_dec(v_toBind_79_);
lean_dec(v_inst_78_);
lean_dec_ref(v___f_76_);
v_toPure_92_ = lean_ctor_get(v_toApplicative_81_, 1);
lean_inc(v_toPure_92_);
lean_dec_ref(v_toApplicative_81_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___boxed(lean_object* v___x_95_, lean_object* v_e_96_, lean_object* v_polarity_97_, lean_object* v___f_98_, lean_object* v_a_99_, lean_object* v_inst_100_, lean_object* v_toBind_101_, lean_object* v___f_102_, lean_object* v_toApplicative_103_, lean_object* v_a_104_){
_start:
{
uint8_t v_polarity_boxed_105_; lean_object* v_res_106_; 
v_polarity_boxed_105_ = lean_unbox(v_polarity_97_);
v_res_106_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2(v___x_95_, v_e_96_, v_polarity_boxed_105_, v___f_98_, v_a_99_, v_inst_100_, v_toBind_101_, v___f_102_, v_toApplicative_103_, v_a_104_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_99_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg(lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_e_115_, uint8_t v_polarity_116_, lean_object* v_x_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_toApplicative_119_; lean_object* v_toBind_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___x_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_toApplicative_119_ = lean_ctor_get(v_inst_113_, 0);
lean_inc_ref(v_toApplicative_119_);
v_toBind_120_ = lean_ctor_get(v_inst_113_, 1);
lean_inc_n(v_toBind_120_, 2);
lean_dec_ref(v_inst_113_);
lean_inc_n(v_a_118_, 3);
v___f_121_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_121_, 0, v_x_117_);
lean_closure_set(v___f_121_, 1, v_a_118_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0));
v___f_123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3));
v___x_124_ = lean_box(v_polarity_116_);
lean_inc(v_inst_114_);
v___f_125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_125_, 0, v___x_122_);
lean_closure_set(v___f_125_, 1, v_e_115_);
lean_closure_set(v___f_125_, 2, v___x_124_);
lean_closure_set(v___f_125_, 3, v___f_123_);
lean_closure_set(v___f_125_, 4, v_a_118_);
lean_closure_set(v___f_125_, 5, v_inst_114_);
lean_closure_set(v___f_125_, 6, v_toBind_120_);
lean_closure_set(v___f_125_, 7, v___f_121_);
lean_closure_set(v___f_125_, 8, v_toApplicative_119_);
v___x_126_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_126_, 0, lean_box(0));
lean_closure_set(v___x_126_, 1, lean_box(0));
lean_closure_set(v___x_126_, 2, v_a_118_);
v___x_127_ = lean_apply_2(v_inst_114_, lean_box(0), v___x_126_);
v___x_128_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_127_, v___f_125_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___boxed(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_e_131_, lean_object* v_polarity_132_, lean_object* v_x_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_polarity_boxed_135_; lean_object* v_res_136_; 
v_polarity_boxed_135_ = lean_unbox(v_polarity_132_);
v_res_136_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg(v_inst_129_, v_inst_130_, v_e_131_, v_polarity_boxed_135_, v_x_133_, v_a_134_);
lean_dec(v_a_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache(lean_object* v_m_137_, lean_object* v_inst_138_, lean_object* v_00_u03c3_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_e_142_, uint8_t v_polarity_143_, lean_object* v_x_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_toApplicative_146_; lean_object* v_toBind_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_toApplicative_146_ = lean_ctor_get(v_inst_138_, 0);
lean_inc_ref(v_toApplicative_146_);
v_toBind_147_ = lean_ctor_get(v_inst_138_, 1);
lean_inc_n(v_toBind_147_, 2);
lean_dec_ref(v_inst_138_);
lean_inc_n(v_a_145_, 3);
v___f_148_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_148_, 0, v_x_144_);
lean_closure_set(v___f_148_, 1, v_a_145_);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0));
v___f_150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3));
v___x_151_ = lean_box(v_polarity_143_);
lean_inc(v_inst_141_);
v___f_152_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_152_, 0, v___x_149_);
lean_closure_set(v___f_152_, 1, v_e_142_);
lean_closure_set(v___f_152_, 2, v___x_151_);
lean_closure_set(v___f_152_, 3, v___f_150_);
lean_closure_set(v___f_152_, 4, v_a_145_);
lean_closure_set(v___f_152_, 5, v_inst_141_);
lean_closure_set(v___f_152_, 6, v_toBind_147_);
lean_closure_set(v___f_152_, 7, v___f_148_);
lean_closure_set(v___f_152_, 8, v_toApplicative_146_);
v___x_153_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, v_a_145_);
v___x_154_ = lean_apply_2(v_inst_141_, lean_box(0), v___x_153_);
v___x_155_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v___x_154_, v___f_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___boxed(lean_object* v_m_156_, lean_object* v_inst_157_, lean_object* v_00_u03c3_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_e_161_, lean_object* v_polarity_162_, lean_object* v_x_163_, lean_object* v_a_164_){
_start:
{
uint8_t v_polarity_boxed_165_; lean_object* v_res_166_; 
v_polarity_boxed_165_ = lean_unbox(v_polarity_162_);
v_res_166_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache(v_m_156_, v_inst_157_, v_00_u03c3_158_, v_inst_159_, v_inst_160_, v_e_161_, v_polarity_boxed_165_, v_x_163_, v_a_164_);
lean_dec(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__2(lean_object* v_toApplicative_167_, lean_object* v_x_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_toPure_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_toPure_170_ = lean_ctor_get(v_toApplicative_167_, 1);
lean_inc(v_toPure_170_);
lean_dec_ref(v_toApplicative_167_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_2(v_toPure_170_, lean_box(0), v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__2___boxed(lean_object* v_toApplicative_173_, lean_object* v_x_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__2(v_toApplicative_173_, v_x_174_, v___y_175_);
lean_dec(v___y_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__7(lean_object* v___f_177_, lean_object* v___f_178_, lean_object* v___x_179_, lean_object* v_s_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_177_, v___f_178_, v_s_180_, v___x_179_, v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9(lean_object* v___x_184_, lean_object* v_e_185_, uint8_t v_polarity_186_, lean_object* v___f_187_, lean_object* v_a_188_, lean_object* v_inst_189_, lean_object* v_toBind_190_, lean_object* v___f_191_, lean_object* v_toApplicative_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___f_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___lam__2___closed__1));
v___f_195_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_195_, 0, v___x_184_);
lean_closure_set(v___f_195_, 1, v___f_194_);
v___x_196_ = lean_box(v_polarity_186_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v_e_185_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
lean_inc_ref(v___x_197_);
lean_inc_ref(v___f_187_);
lean_inc_ref(v___f_195_);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_195_, v___f_187_, v_a_193_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec_ref(v_toApplicative_192_);
v___f_199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__7), 4, 3);
lean_closure_set(v___f_199_, 0, v___f_195_);
lean_closure_set(v___f_199_, 1, v___f_187_);
lean_closure_set(v___f_199_, 2, v___x_197_);
lean_inc(v_a_188_);
v___x_200_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, lean_box(0));
lean_closure_set(v___x_200_, 2, lean_box(0));
lean_closure_set(v___x_200_, 3, v_a_188_);
lean_closure_set(v___x_200_, 4, v___f_199_);
v___x_201_ = lean_apply_2(v_inst_189_, lean_box(0), v___x_200_);
v___x_202_ = lean_apply_4(v_toBind_190_, lean_box(0), lean_box(0), v___x_201_, v___f_191_);
return v___x_202_;
}
else
{
lean_object* v_toPure_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref_known(v___x_197_, 2);
lean_dec_ref(v___f_195_);
lean_dec(v___f_191_);
lean_dec(v_toBind_190_);
lean_dec(v_inst_189_);
lean_dec_ref(v___f_187_);
v_toPure_203_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc(v_toPure_203_);
lean_dec_ref(v_toApplicative_192_);
v___x_204_ = lean_box(0);
v___x_205_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9___boxed(lean_object* v___x_206_, lean_object* v_e_207_, lean_object* v_polarity_208_, lean_object* v___f_209_, lean_object* v_a_210_, lean_object* v_inst_211_, lean_object* v_toBind_212_, lean_object* v___f_213_, lean_object* v_toApplicative_214_, lean_object* v_a_215_){
_start:
{
uint8_t v_polarity_boxed_216_; lean_object* v_res_217_; 
v_polarity_boxed_216_ = lean_unbox(v_polarity_208_);
v_res_217_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9(v___x_206_, v_e_207_, v_polarity_boxed_216_, v___f_209_, v_a_210_, v_inst_211_, v_toBind_212_, v___f_213_, v_toApplicative_214_, v_a_215_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_210_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__0___boxed(lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_q_221_, lean_object* v_polarity_222_, lean_object* v_f_223_, lean_object* v___y_224_, lean_object* v_a_225_){
_start:
{
uint8_t v_polarity_boxed_226_; lean_object* v_res_227_; 
v_polarity_boxed_226_ = lean_unbox(v_polarity_222_);
v_res_227_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__0(v_inst_218_, v_inst_219_, v_inst_220_, v_q_221_, v_polarity_boxed_226_, v_f_223_, v___y_224_, v_a_225_);
lean_dec(v___y_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__1(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, uint8_t v_polarity_231_, lean_object* v_f_232_, lean_object* v_toBind_233_, lean_object* v_p_234_, lean_object* v_q_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_237_ = lean_box(v_polarity_231_);
lean_inc(v___y_236_);
lean_inc(v_f_232_);
lean_inc(v_inst_230_);
lean_inc_ref(v_inst_228_);
v___f_238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_238_, 0, v_inst_228_);
lean_closure_set(v___f_238_, 1, v_inst_229_);
lean_closure_set(v___f_238_, 2, v_inst_230_);
lean_closure_set(v___f_238_, 3, v_q_235_);
lean_closure_set(v___f_238_, 4, v___x_237_);
lean_closure_set(v___f_238_, 5, v_f_232_);
lean_closure_set(v___f_238_, 6, v___y_236_);
v___x_239_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_228_, v_inst_229_, v_inst_230_, v_p_234_, v_polarity_231_, v_f_232_, v___y_236_);
v___x_240_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_239_, v___f_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__1___boxed(lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_inst_243_, lean_object* v_polarity_244_, lean_object* v_f_245_, lean_object* v_toBind_246_, lean_object* v_p_247_, lean_object* v_q_248_, lean_object* v___y_249_){
_start:
{
uint8_t v_polarity_boxed_250_; lean_object* v_res_251_; 
v_polarity_boxed_250_ = lean_unbox(v_polarity_244_);
v_res_251_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__1(v_inst_241_, v_inst_242_, v_inst_243_, v_polarity_boxed_250_, v_f_245_, v_toBind_246_, v_p_247_, v_q_248_, v___y_249_);
lean_dec(v___y_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_arg_281_, uint8_t v_polarity_282_, lean_object* v_f_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_278_, v_inst_279_, v_inst_280_, v_arg_281_, v_polarity_282_, v_f_283_, v_a_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3___boxed(lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_arg_290_, lean_object* v_polarity_291_, lean_object* v_f_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
uint8_t v_polarity_boxed_295_; lean_object* v_res_296_; 
v_polarity_boxed_295_ = lean_unbox(v_polarity_291_);
v_res_296_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3(v_inst_287_, v_inst_288_, v_inst_289_, v_arg_290_, v_polarity_boxed_295_, v_f_292_, v_a_293_, v_a_294_);
lean_dec(v_a_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4(lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_arg_300_, uint8_t v_polarity_301_, lean_object* v_f_302_, lean_object* v_a_303_, lean_object* v_toBind_304_, lean_object* v___f_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_297_, v_inst_298_, v_inst_299_, v_arg_300_, v_polarity_301_, v_f_302_, v_a_303_);
v___x_308_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_307_, v___f_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4___boxed(lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_arg_312_, lean_object* v_polarity_313_, lean_object* v_f_314_, lean_object* v_a_315_, lean_object* v_toBind_316_, lean_object* v___f_317_, lean_object* v_a_318_){
_start:
{
uint8_t v_polarity_boxed_319_; lean_object* v_res_320_; 
v_polarity_boxed_319_ = lean_unbox(v_polarity_313_);
v_res_320_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4(v_inst_309_, v_inst_310_, v_inst_311_, v_arg_312_, v_polarity_boxed_319_, v_f_314_, v_a_315_, v_toBind_316_, v___f_317_, v_a_318_);
lean_dec(v_a_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__1(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_q_324_, uint8_t v_polarity_325_, lean_object* v_f_326_, lean_object* v___y_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_321_, v_inst_322_, v_inst_323_, v_q_324_, v_polarity_325_, v_f_326_, v___y_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__1___boxed(lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_q_333_, lean_object* v_polarity_334_, lean_object* v_f_335_, lean_object* v___y_336_, lean_object* v_a_337_){
_start:
{
uint8_t v_polarity_boxed_338_; lean_object* v_res_339_; 
v_polarity_boxed_338_ = lean_unbox(v_polarity_334_);
v_res_339_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__1(v_inst_330_, v_inst_331_, v_inst_332_, v_q_333_, v_polarity_boxed_338_, v_f_335_, v___y_336_, v_a_337_);
lean_dec(v___y_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__0(lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_body_343_, uint8_t v_polarity_344_, lean_object* v_f_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_340_, v_inst_341_, v_inst_342_, v_body_343_, v_polarity_344_, v_f_345_, v_a_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__0___boxed(lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_body_352_, lean_object* v_polarity_353_, lean_object* v_f_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
uint8_t v_polarity_boxed_357_; lean_object* v_res_358_; 
v_polarity_boxed_357_ = lean_unbox(v_polarity_353_);
v_res_358_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__0(v_inst_349_, v_inst_350_, v_inst_351_, v_body_352_, v_polarity_boxed_357_, v_f_354_, v_a_355_, v_a_356_);
lean_dec(v_a_355_);
return v_res_358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__3(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__2));
v___x_363_ = lean_unsigned_to_nat(6u);
v___x_364_ = lean_unsigned_to_nat(114u);
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__1));
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__0));
v___x_367_ = l_mkPanicMessageWithDecl(v___x_366_, v___x_365_, v___x_364_, v___x_363_, v___x_362_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_arg_386_, uint8_t v_polarity_387_, lean_object* v_f_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_383_, v_inst_384_, v_inst_385_, v_arg_386_, v_polarity_387_, v_f_388_, v_a_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2___boxed(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_arg_395_, lean_object* v_polarity_396_, lean_object* v_f_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
uint8_t v_polarity_boxed_400_; lean_object* v_res_401_; 
v_polarity_boxed_400_ = lean_unbox(v_polarity_396_);
v_res_401_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2(v_inst_392_, v_inst_393_, v_inst_394_, v_arg_395_, v_polarity_boxed_400_, v_f_397_, v_a_398_, v_a_399_);
lean_dec(v_a_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_arg_405_, uint8_t v_polarity_406_, lean_object* v_f_407_, lean_object* v_a_408_, lean_object* v_toBind_409_, lean_object* v___f_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_402_, v_inst_403_, v_inst_404_, v_arg_405_, v_polarity_406_, v_f_407_, v_a_408_);
v___x_413_ = lean_apply_4(v_toBind_409_, lean_box(0), lean_box(0), v___x_412_, v___f_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3___boxed(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_arg_417_, lean_object* v_polarity_418_, lean_object* v_f_419_, lean_object* v_a_420_, lean_object* v_toBind_421_, lean_object* v___f_422_, lean_object* v_a_423_){
_start:
{
uint8_t v_polarity_boxed_424_; lean_object* v_res_425_; 
v_polarity_boxed_424_ = lean_unbox(v_polarity_418_);
v_res_425_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3(v_inst_414_, v_inst_415_, v_inst_416_, v_arg_417_, v_polarity_boxed_424_, v_f_419_, v_a_420_, v_toBind_421_, v___f_422_, v_a_423_);
lean_dec(v_a_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8(lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_arg_429_, uint8_t v___x_430_, lean_object* v_f_431_, lean_object* v_a_432_, lean_object* v_toBind_433_, lean_object* v___f_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_426_, v_inst_427_, v_inst_428_, v_arg_429_, v___x_430_, v_f_431_, v_a_432_);
v___x_437_ = lean_apply_4(v_toBind_433_, lean_box(0), lean_box(0), v___x_436_, v___f_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8___boxed(lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_arg_441_, lean_object* v___x_442_, lean_object* v_f_443_, lean_object* v_a_444_, lean_object* v_toBind_445_, lean_object* v___f_446_, lean_object* v_a_447_){
_start:
{
uint8_t v___x_3610__boxed_448_; lean_object* v_res_449_; 
v___x_3610__boxed_448_ = lean_unbox(v___x_442_);
v_res_449_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8(v_inst_438_, v_inst_439_, v_inst_440_, v_arg_441_, v___x_3610__boxed_448_, v_f_443_, v_a_444_, v_toBind_445_, v___f_446_, v_a_447_);
lean_dec(v_a_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__0(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_q_458_, uint8_t v___x_459_, lean_object* v_f_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_455_, v_inst_456_, v_inst_457_, v_q_458_, v___x_459_, v_f_460_, v_a_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__0___boxed(lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_q_467_, lean_object* v___x_468_, lean_object* v_f_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
uint8_t v___x_3569__boxed_472_; lean_object* v_res_473_; 
v___x_3569__boxed_472_ = lean_unbox(v___x_468_);
v_res_473_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__0(v_inst_464_, v_inst_465_, v_inst_466_, v_q_467_, v___x_3569__boxed_472_, v_f_469_, v_a_470_, v_a_471_);
lean_dec(v_a_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__1(lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_q_477_, uint8_t v___x_478_, lean_object* v_f_479_, lean_object* v_a_480_, lean_object* v_toBind_481_, lean_object* v___f_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_474_, v_inst_475_, v_inst_476_, v_q_477_, v___x_478_, v_f_479_, v_a_480_);
v___x_485_ = lean_apply_4(v_toBind_481_, lean_box(0), lean_box(0), v___x_484_, v___f_482_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__1___boxed(lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_q_489_, lean_object* v___x_490_, lean_object* v_f_491_, lean_object* v_a_492_, lean_object* v_toBind_493_, lean_object* v___f_494_, lean_object* v_a_495_){
_start:
{
uint8_t v___x_3617__boxed_496_; lean_object* v_res_497_; 
v___x_3617__boxed_496_ = lean_unbox(v___x_490_);
v_res_497_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__1(v_inst_486_, v_inst_487_, v_inst_488_, v_q_489_, v___x_3617__boxed_496_, v_f_491_, v_a_492_, v_toBind_493_, v___f_494_, v_a_495_);
lean_dec(v_a_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__2(lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_p_501_, uint8_t v___x_502_, lean_object* v_f_503_, lean_object* v_a_504_, lean_object* v_toBind_505_, lean_object* v___f_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_498_, v_inst_499_, v_inst_500_, v_p_501_, v___x_502_, v_f_503_, v_a_504_);
v___x_509_ = lean_apply_4(v_toBind_505_, lean_box(0), lean_box(0), v___x_508_, v___f_506_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__2___boxed(lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_p_513_, lean_object* v___x_514_, lean_object* v_f_515_, lean_object* v_a_516_, lean_object* v_toBind_517_, lean_object* v___f_518_, lean_object* v_a_519_){
_start:
{
uint8_t v___x_3624__boxed_520_; lean_object* v_res_521_; 
v___x_3624__boxed_520_ = lean_unbox(v___x_514_);
v_res_521_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__2(v_inst_510_, v_inst_511_, v_inst_512_, v_p_513_, v___x_3624__boxed_520_, v_f_515_, v_a_516_, v_toBind_517_, v___f_518_, v_a_519_);
lean_dec(v_a_516_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_p_525_, lean_object* v_q_526_, uint8_t v_polarity_527_, uint8_t v_flip_528_, lean_object* v_f_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; uint8_t v___y_538_; 
v___x_534_ = l_Lean_Expr_cleanupAnnotations(v_p_525_);
v___x_535_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2));
v___x_536_ = l_Lean_Expr_isConstOf(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__1));
v___x_542_ = l_Lean_Expr_isConstOf(v___x_534_, v___x_541_);
lean_dec_ref(v___x_534_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___y_546_; 
v___x_543_ = l_Lean_Expr_cleanupAnnotations(v_q_526_);
v___x_544_ = l_Lean_Expr_isConstOf(v___x_543_, v___x_535_);
if (v___x_544_ == 0)
{
uint8_t v___x_551_; 
v___x_551_ = l_Lean_Expr_isConstOf(v___x_543_, v___x_541_);
lean_dec_ref(v___x_543_);
if (v___x_551_ == 0)
{
lean_object* v_toBind_552_; lean_object* v___x_553_; lean_object* v___f_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_toBind_552_ = lean_ctor_get(v_inst_522_, 1);
lean_inc_n(v_toBind_552_, 3);
v___x_553_ = lean_box(v___x_551_);
lean_inc_n(v_a_530_, 3);
lean_inc_n(v_f_529_, 3);
lean_inc_ref(v_q_526_);
lean_inc_n(v_inst_524_, 3);
lean_inc_ref_n(v_inst_522_, 3);
v___f_554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_554_, 0, v_inst_522_);
lean_closure_set(v___f_554_, 1, v_inst_523_);
lean_closure_set(v___f_554_, 2, v_inst_524_);
lean_closure_set(v___f_554_, 3, v_q_526_);
lean_closure_set(v___f_554_, 4, v___x_553_);
lean_closure_set(v___f_554_, 5, v_f_529_);
lean_closure_set(v___f_554_, 6, v_a_530_);
v___x_555_ = 1;
v___x_556_ = lean_box(v___x_555_);
v___f_557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_557_, 0, v_inst_522_);
lean_closure_set(v___f_557_, 1, v_inst_523_);
lean_closure_set(v___f_557_, 2, v_inst_524_);
lean_closure_set(v___f_557_, 3, v_q_526_);
lean_closure_set(v___f_557_, 4, v___x_556_);
lean_closure_set(v___f_557_, 5, v_f_529_);
lean_closure_set(v___f_557_, 6, v_a_530_);
lean_closure_set(v___f_557_, 7, v_toBind_552_);
lean_closure_set(v___f_557_, 8, v___f_554_);
v___x_558_ = lean_box(v___x_551_);
lean_inc_ref(v_p_525_);
v___f_559_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_559_, 0, v_inst_522_);
lean_closure_set(v___f_559_, 1, v_inst_523_);
lean_closure_set(v___f_559_, 2, v_inst_524_);
lean_closure_set(v___f_559_, 3, v_p_525_);
lean_closure_set(v___f_559_, 4, v___x_558_);
lean_closure_set(v___f_559_, 5, v_f_529_);
lean_closure_set(v___f_559_, 6, v_a_530_);
lean_closure_set(v___f_559_, 7, v_toBind_552_);
lean_closure_set(v___f_559_, 8, v___f_557_);
v___x_560_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_555_, v_f_529_, v_a_530_);
v___x_561_ = lean_apply_4(v_toBind_552_, lean_box(0), lean_box(0), v___x_560_, v___f_559_);
return v___x_561_;
}
else
{
lean_dec_ref(v_q_526_);
if (v_flip_528_ == 0)
{
if (v_polarity_527_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_544_, v_f_529_, v_a_530_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_551_, v_f_529_, v_a_530_);
return v___x_563_;
}
}
else
{
if (v_polarity_527_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_551_, v_f_529_, v_a_530_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_544_, v_f_529_, v_a_530_);
return v___x_565_;
}
}
}
}
else
{
lean_dec_ref(v___x_543_);
lean_dec_ref(v_q_526_);
if (v_polarity_527_ == 0)
{
v___y_546_ = v___x_544_;
goto v___jp_545_;
}
else
{
v___y_546_ = v___x_542_;
goto v___jp_545_;
}
}
v___jp_545_:
{
if (v_flip_528_ == 0)
{
if (v___y_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_542_, v_f_529_, v_a_530_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_544_, v_f_529_, v_a_530_);
return v___x_548_;
}
}
else
{
if (v___y_546_ == 0)
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_544_, v_f_529_, v_a_530_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_p_525_, v___x_542_, v_f_529_, v_a_530_);
return v___x_550_;
}
}
}
}
else
{
lean_dec_ref(v_p_525_);
if (v_flip_528_ == 0)
{
if (v_polarity_527_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_536_, v_f_529_, v_a_530_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_542_, v_f_529_, v_a_530_);
return v___x_567_;
}
}
else
{
if (v_polarity_527_ == 0)
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_542_, v_f_529_, v_a_530_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_536_, v_f_529_, v_a_530_);
return v___x_569_;
}
}
}
}
else
{
lean_dec_ref(v___x_534_);
lean_dec_ref(v_p_525_);
if (v_polarity_527_ == 0)
{
v___y_538_ = v___x_536_;
goto v___jp_537_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = 0;
v___y_538_ = v___x_570_;
goto v___jp_537_;
}
}
v___jp_531_:
{
uint8_t v___x_532_; lean_object* v___x_533_; 
v___x_532_ = 0;
v___x_533_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_532_, v_f_529_, v_a_530_);
return v___x_533_;
}
v___jp_537_:
{
if (v_flip_528_ == 0)
{
if (v___y_538_ == 0)
{
goto v___jp_531_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_536_, v_f_529_, v_a_530_);
return v___x_539_;
}
}
else
{
if (v___y_538_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_522_, v_inst_523_, v_inst_524_, v_q_526_, v___x_536_, v_f_529_, v_a_530_);
return v___x_540_;
}
else
{
goto v___jp_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__0(lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_q_580_, uint8_t v___x_581_, lean_object* v_f_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_577_, v_inst_578_, v_inst_579_, v_q_580_, v___x_581_, v_f_582_, v_a_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__0___boxed(lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_q_589_, lean_object* v___x_590_, lean_object* v_f_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
uint8_t v___x_3589__boxed_594_; lean_object* v_res_595_; 
v___x_3589__boxed_594_ = lean_unbox(v___x_590_);
v_res_595_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__0(v_inst_586_, v_inst_587_, v_inst_588_, v_q_589_, v___x_3589__boxed_594_, v_f_591_, v_a_592_, v_a_593_);
lean_dec(v_a_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__1(lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_q_599_, uint8_t v___x_600_, lean_object* v_f_601_, lean_object* v_a_602_, lean_object* v_toBind_603_, lean_object* v___f_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_596_, v_inst_597_, v_inst_598_, v_q_599_, v___x_600_, v_f_601_, v_a_602_);
v___x_607_ = lean_apply_4(v_toBind_603_, lean_box(0), lean_box(0), v___x_606_, v___f_604_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__1___boxed(lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_q_611_, lean_object* v___x_612_, lean_object* v_f_613_, lean_object* v_a_614_, lean_object* v_toBind_615_, lean_object* v___f_616_, lean_object* v_a_617_){
_start:
{
uint8_t v___x_3638__boxed_618_; lean_object* v_res_619_; 
v___x_3638__boxed_618_ = lean_unbox(v___x_612_);
v_res_619_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__1(v_inst_608_, v_inst_609_, v_inst_610_, v_q_611_, v___x_3638__boxed_618_, v_f_613_, v_a_614_, v_toBind_615_, v___f_616_, v_a_617_);
lean_dec(v_a_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__2(lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_p_623_, uint8_t v___x_624_, lean_object* v_f_625_, lean_object* v_a_626_, lean_object* v_toBind_627_, lean_object* v___f_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_620_, v_inst_621_, v_inst_622_, v_p_623_, v___x_624_, v_f_625_, v_a_626_);
v___x_631_ = lean_apply_4(v_toBind_627_, lean_box(0), lean_box(0), v___x_630_, v___f_628_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__2___boxed(lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_p_635_, lean_object* v___x_636_, lean_object* v_f_637_, lean_object* v_a_638_, lean_object* v_toBind_639_, lean_object* v___f_640_, lean_object* v_a_641_){
_start:
{
uint8_t v___x_3645__boxed_642_; lean_object* v_res_643_; 
v___x_3645__boxed_642_ = lean_unbox(v___x_636_);
v_res_643_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__2(v_inst_632_, v_inst_633_, v_inst_634_, v_p_635_, v___x_3645__boxed_642_, v_f_637_, v_a_638_, v_toBind_639_, v___f_640_, v_a_641_);
lean_dec(v_a_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_p_647_, lean_object* v_q_648_, uint8_t v_polarity_649_, uint8_t v_flip_650_, lean_object* v_f_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; uint8_t v___y_660_; 
v___x_656_ = l_Lean_Expr_cleanupAnnotations(v_p_647_);
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__1));
v___x_658_ = l_Lean_Expr_isConstOf(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___closed__3));
v___x_664_ = l_Lean_Expr_isConstOf(v___x_656_, v___x_663_);
lean_dec_ref(v___x_656_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; uint8_t v___x_666_; uint8_t v___y_668_; 
v___x_665_ = l_Lean_Expr_cleanupAnnotations(v_q_648_);
v___x_666_ = l_Lean_Expr_isConstOf(v___x_665_, v___x_657_);
if (v___x_666_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = l_Lean_Expr_isConstOf(v___x_665_, v___x_663_);
lean_dec_ref(v___x_665_);
if (v___x_673_ == 0)
{
lean_object* v_toBind_674_; lean_object* v___x_675_; lean_object* v___f_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___f_679_; lean_object* v___x_680_; lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_toBind_674_ = lean_ctor_get(v_inst_644_, 1);
lean_inc_n(v_toBind_674_, 3);
v___x_675_ = lean_box(v___x_673_);
lean_inc_n(v_a_652_, 3);
lean_inc_n(v_f_651_, 3);
lean_inc_ref(v_q_648_);
lean_inc_n(v_inst_646_, 3);
lean_inc_ref_n(v_inst_644_, 3);
v___f_676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_676_, 0, v_inst_644_);
lean_closure_set(v___f_676_, 1, v_inst_645_);
lean_closure_set(v___f_676_, 2, v_inst_646_);
lean_closure_set(v___f_676_, 3, v_q_648_);
lean_closure_set(v___f_676_, 4, v___x_675_);
lean_closure_set(v___f_676_, 5, v_f_651_);
lean_closure_set(v___f_676_, 6, v_a_652_);
v___x_677_ = 1;
v___x_678_ = lean_box(v___x_677_);
v___f_679_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__1___boxed), 10, 9);
lean_closure_set(v___f_679_, 0, v_inst_644_);
lean_closure_set(v___f_679_, 1, v_inst_645_);
lean_closure_set(v___f_679_, 2, v_inst_646_);
lean_closure_set(v___f_679_, 3, v_q_648_);
lean_closure_set(v___f_679_, 4, v___x_678_);
lean_closure_set(v___f_679_, 5, v_f_651_);
lean_closure_set(v___f_679_, 6, v_a_652_);
lean_closure_set(v___f_679_, 7, v_toBind_674_);
lean_closure_set(v___f_679_, 8, v___f_676_);
v___x_680_ = lean_box(v___x_673_);
lean_inc_ref(v_p_647_);
v___f_681_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_681_, 0, v_inst_644_);
lean_closure_set(v___f_681_, 1, v_inst_645_);
lean_closure_set(v___f_681_, 2, v_inst_646_);
lean_closure_set(v___f_681_, 3, v_p_647_);
lean_closure_set(v___f_681_, 4, v___x_680_);
lean_closure_set(v___f_681_, 5, v_f_651_);
lean_closure_set(v___f_681_, 6, v_a_652_);
lean_closure_set(v___f_681_, 7, v_toBind_674_);
lean_closure_set(v___f_681_, 8, v___f_679_);
v___x_682_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_677_, v_f_651_, v_a_652_);
v___x_683_ = lean_apply_4(v_toBind_674_, lean_box(0), lean_box(0), v___x_682_, v___f_681_);
return v___x_683_;
}
else
{
lean_dec_ref(v_q_648_);
if (v_flip_650_ == 0)
{
if (v_polarity_649_ == 0)
{
lean_object* v___x_684_; 
v___x_684_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_666_, v_f_651_, v_a_652_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_673_, v_f_651_, v_a_652_);
return v___x_685_;
}
}
else
{
if (v_polarity_649_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_673_, v_f_651_, v_a_652_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; 
v___x_687_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_666_, v_f_651_, v_a_652_);
return v___x_687_;
}
}
}
}
else
{
lean_dec_ref(v___x_665_);
lean_dec_ref(v_q_648_);
if (v_polarity_649_ == 0)
{
v___y_668_ = v___x_666_;
goto v___jp_667_;
}
else
{
v___y_668_ = v___x_664_;
goto v___jp_667_;
}
}
v___jp_667_:
{
if (v_flip_650_ == 0)
{
if (v___y_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_664_, v_f_651_, v_a_652_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_666_, v_f_651_, v_a_652_);
return v___x_670_;
}
}
else
{
if (v___y_668_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_666_, v_f_651_, v_a_652_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_p_647_, v___x_664_, v_f_651_, v_a_652_);
return v___x_672_;
}
}
}
}
else
{
lean_dec_ref(v_p_647_);
if (v_flip_650_ == 0)
{
if (v_polarity_649_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_658_, v_f_651_, v_a_652_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_664_, v_f_651_, v_a_652_);
return v___x_689_;
}
}
else
{
if (v_polarity_649_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_664_, v_f_651_, v_a_652_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_658_, v_f_651_, v_a_652_);
return v___x_691_;
}
}
}
}
else
{
lean_dec_ref(v___x_656_);
lean_dec_ref(v_p_647_);
if (v_polarity_649_ == 0)
{
v___y_660_ = v___x_658_;
goto v___jp_659_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 0;
v___y_660_ = v___x_692_;
goto v___jp_659_;
}
}
v___jp_653_:
{
uint8_t v___x_654_; lean_object* v___x_655_; 
v___x_654_ = 0;
v___x_655_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_654_, v_f_651_, v_a_652_);
return v___x_655_;
}
v___jp_659_:
{
if (v_flip_650_ == 0)
{
if (v___y_660_ == 0)
{
goto v___jp_653_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_658_, v_f_651_, v_a_652_);
return v___x_661_;
}
}
else
{
if (v___y_660_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_644_, v_inst_645_, v_inst_646_, v_q_648_, v___x_658_, v_f_651_, v_a_652_);
return v___x_662_;
}
else
{
goto v___jp_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8(lean_object* v_e_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, uint8_t v_polarity_697_, lean_object* v_f_698_, lean_object* v_a_699_, lean_object* v_toBind_700_, lean_object* v___x_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_p_704_; lean_object* v_q_705_; lean_object* v___y_706_; 
if (lean_obj_tag(v_e_693_) == 7)
{
lean_object* v_binderType_711_; lean_object* v_body_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_binderType_711_ = lean_ctor_get(v_e_693_, 1);
lean_inc_ref(v_binderType_711_);
v_body_712_ = lean_ctor_get(v_e_693_, 2);
lean_inc_ref(v_body_712_);
lean_dec_ref_known(v_e_693_, 3);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_expr_has_loose_bvar(v_body_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___f_716_; uint8_t v___y_718_; 
v___x_715_ = lean_box(v_polarity_697_);
lean_inc(v_a_699_);
lean_inc(v_f_698_);
lean_inc(v_inst_696_);
lean_inc_ref(v_inst_694_);
v___f_716_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_716_, 0, v_inst_694_);
lean_closure_set(v___f_716_, 1, v_inst_695_);
lean_closure_set(v___f_716_, 2, v_inst_696_);
lean_closure_set(v___f_716_, 3, v_body_712_);
lean_closure_set(v___f_716_, 4, v___x_715_);
lean_closure_set(v___f_716_, 5, v_f_698_);
lean_closure_set(v___f_716_, 6, v_a_699_);
if (v_polarity_697_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = 1;
v___y_718_ = v___x_721_;
goto v___jp_717_;
}
else
{
v___y_718_ = v___x_714_;
goto v___jp_717_;
}
v___jp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_binderType_711_, v___y_718_, v_f_698_, v_a_699_);
v___x_720_ = lean_apply_4(v_toBind_700_, lean_box(0), lean_box(0), v___x_719_, v___f_716_);
return v___x_720_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_3297__overap_723_; lean_object* v___x_724_; 
lean_dec_ref(v_body_712_);
lean_dec_ref(v_binderType_711_);
lean_dec(v_toBind_700_);
lean_dec(v_f_698_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__3);
v___x_3297__overap_723_ = l_panic___redArg(v___x_701_, v___x_722_);
lean_inc(v_a_699_);
v___x_724_ = lean_apply_1(v___x_3297__overap_723_, v_a_699_);
return v___x_724_;
}
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = l_Lean_Expr_cleanupAnnotations(v_e_693_);
v___x_726_ = l_Lean_Expr_isApp(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v___x_725_);
lean_dec(v_toBind_700_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_727_ = lean_box(v_polarity_697_);
v___x_728_ = lean_apply_2(v_f_698_, v_e_693_, v___x_727_);
return v___x_728_;
}
else
{
lean_object* v_arg_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_arg_729_ = lean_ctor_get(v___x_725_, 1);
lean_inc_ref(v_arg_729_);
v___x_730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_725_);
lean_dec_ref(v___x_725_);
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__5));
v___x_732_ = l_Lean_Expr_isConstOf(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Expr_isApp(v___x_730_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref(v___x_730_);
lean_dec_ref(v_arg_729_);
lean_dec(v_toBind_700_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_734_ = lean_box(v_polarity_697_);
v___x_735_ = lean_apply_2(v_f_698_, v_e_693_, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v_arg_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_arg_736_ = lean_ctor_get(v___x_730_, 1);
lean_inc_ref(v_arg_736_);
v___x_737_ = l_Lean_Expr_appFnCleanup___redArg(v___x_730_);
lean_dec_ref(v___x_730_);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__7));
v___x_739_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__9));
v___x_741_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__11));
v___x_743_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_742_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; 
v___x_744_ = l_Lean_Expr_isApp(v___x_737_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v___x_737_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_729_);
lean_dec(v_toBind_700_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_745_ = lean_box(v_polarity_697_);
v___x_746_ = lean_apply_2(v_f_698_, v_e_693_, v___x_745_);
return v___x_746_;
}
else
{
lean_object* v_arg_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_arg_747_ = lean_ctor_get(v___x_737_, 1);
lean_inc_ref(v_arg_747_);
v___x_748_ = l_Lean_Expr_appFnCleanup___redArg(v___x_737_);
lean_dec_ref(v___x_737_);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__13));
v___x_750_ = l_Lean_Expr_isConstOf(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
uint8_t v___x_751_; 
v___x_751_ = l_Lean_Expr_isApp(v___x_748_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v___x_748_);
lean_dec_ref(v_arg_747_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_729_);
lean_dec(v_toBind_700_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_752_ = lean_box(v_polarity_697_);
v___x_753_ = lean_apply_2(v_f_698_, v_e_693_, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = l_Lean_Expr_appFnCleanup___redArg(v___x_748_);
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__8));
v___x_756_ = l_Lean_Expr_isConstOf(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; 
lean_dec_ref(v_arg_747_);
v___x_757_ = l_Lean_Expr_isApp(v___x_754_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v___x_754_);
lean_dec_ref(v___x_748_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_729_);
lean_dec(v_toBind_700_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_758_ = lean_box(v_polarity_697_);
v___x_759_ = lean_apply_2(v_f_698_, v_e_693_, v___x_758_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_754_);
lean_dec_ref(v___x_754_);
v___x_761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__13));
v___x_762_ = l_Lean_Expr_isConstOf(v___x_760_, v___x_761_);
lean_dec_ref(v___x_760_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_748_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_729_);
lean_dec(v_toBind_700_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_763_ = lean_box(v_polarity_697_);
v___x_764_ = lean_apply_2(v_f_698_, v_e_693_, v___x_763_);
return v___x_764_;
}
else
{
lean_object* v_arg_765_; lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_e_693_);
v_arg_765_ = lean_ctor_get(v___x_748_, 1);
lean_inc_ref_n(v_arg_765_, 2);
lean_dec_ref(v___x_748_);
v___x_766_ = lean_box(v_polarity_697_);
lean_inc_n(v_a_699_, 3);
lean_inc_n(v_f_698_, 3);
lean_inc_n(v_inst_696_, 3);
lean_inc_ref_n(v_inst_694_, 3);
v___f_767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_767_, 0, v_inst_694_);
lean_closure_set(v___f_767_, 1, v_inst_695_);
lean_closure_set(v___f_767_, 2, v_inst_696_);
lean_closure_set(v___f_767_, 3, v_arg_729_);
lean_closure_set(v___f_767_, 4, v___x_766_);
lean_closure_set(v___f_767_, 5, v_f_698_);
lean_closure_set(v___f_767_, 6, v_a_699_);
v___x_768_ = lean_box(v_polarity_697_);
lean_inc_n(v_toBind_700_, 2);
v___f_769_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_769_, 0, v_inst_694_);
lean_closure_set(v___f_769_, 1, v_inst_695_);
lean_closure_set(v___f_769_, 2, v_inst_696_);
lean_closure_set(v___f_769_, 3, v_arg_736_);
lean_closure_set(v___f_769_, 4, v___x_768_);
lean_closure_set(v___f_769_, 5, v_f_698_);
lean_closure_set(v___f_769_, 6, v_a_699_);
lean_closure_set(v___f_769_, 7, v_toBind_700_);
lean_closure_set(v___f_769_, 8, v___f_767_);
v___x_770_ = lean_box(v___x_756_);
v___f_771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_771_, 0, v_inst_694_);
lean_closure_set(v___f_771_, 1, v_inst_695_);
lean_closure_set(v___f_771_, 2, v_inst_696_);
lean_closure_set(v___f_771_, 3, v_arg_765_);
lean_closure_set(v___f_771_, 4, v___x_770_);
lean_closure_set(v___f_771_, 5, v_f_698_);
lean_closure_set(v___f_771_, 6, v_a_699_);
lean_closure_set(v___f_771_, 7, v_toBind_700_);
lean_closure_set(v___f_771_, 8, v___f_769_);
v___x_772_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_765_, v___x_762_, v_f_698_, v_a_699_);
v___x_773_ = lean_apply_4(v_toBind_700_, lean_box(0), lean_box(0), v___x_772_, v___f_771_);
return v___x_773_;
}
}
}
else
{
lean_object* v___x_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v___x_754_);
lean_dec_ref(v___x_748_);
lean_dec_ref(v_e_693_);
v___x_774_ = lean_box(v_polarity_697_);
lean_inc_n(v_a_699_, 3);
lean_inc_n(v_f_698_, 3);
lean_inc_n(v_inst_696_, 3);
lean_inc_ref_n(v_inst_694_, 3);
v___f_775_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_775_, 0, v_inst_694_);
lean_closure_set(v___f_775_, 1, v_inst_695_);
lean_closure_set(v___f_775_, 2, v_inst_696_);
lean_closure_set(v___f_775_, 3, v_arg_729_);
lean_closure_set(v___f_775_, 4, v___x_774_);
lean_closure_set(v___f_775_, 5, v_f_698_);
lean_closure_set(v___f_775_, 6, v_a_699_);
v___x_776_ = lean_box(v_polarity_697_);
lean_inc_n(v_toBind_700_, 2);
v___f_777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_777_, 0, v_inst_694_);
lean_closure_set(v___f_777_, 1, v_inst_695_);
lean_closure_set(v___f_777_, 2, v_inst_696_);
lean_closure_set(v___f_777_, 3, v_arg_736_);
lean_closure_set(v___f_777_, 4, v___x_776_);
lean_closure_set(v___f_777_, 5, v_f_698_);
lean_closure_set(v___f_777_, 6, v_a_699_);
lean_closure_set(v___f_777_, 7, v_toBind_700_);
lean_closure_set(v___f_777_, 8, v___f_775_);
v___x_778_ = lean_box(v___x_750_);
lean_inc_ref(v_arg_747_);
v___f_779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_779_, 0, v_inst_694_);
lean_closure_set(v___f_779_, 1, v_inst_695_);
lean_closure_set(v___f_779_, 2, v_inst_696_);
lean_closure_set(v___f_779_, 3, v_arg_747_);
lean_closure_set(v___f_779_, 4, v___x_778_);
lean_closure_set(v___f_779_, 5, v_f_698_);
lean_closure_set(v___f_779_, 6, v_a_699_);
lean_closure_set(v___f_779_, 7, v_toBind_700_);
lean_closure_set(v___f_779_, 8, v___f_777_);
v___x_780_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_747_, v___x_756_, v_f_698_, v_a_699_);
v___x_781_ = lean_apply_4(v_toBind_700_, lean_box(0), lean_box(0), v___x_780_, v___f_779_);
return v___x_781_;
}
}
}
else
{
uint8_t v___x_782_; 
lean_dec_ref(v___x_748_);
lean_dec(v_toBind_700_);
v___x_782_ = l_Lean_Expr_isProp(v_arg_747_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___closed__14));
v___x_784_ = l_Lean_Expr_isConstOf(v_arg_747_, v___x_783_);
lean_dec_ref(v_arg_747_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_729_);
lean_dec(v_inst_696_);
lean_dec_ref(v_inst_694_);
v___x_785_ = lean_box(v_polarity_697_);
v___x_786_ = lean_apply_2(v_f_698_, v_e_693_, v___x_785_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v_e_693_);
v___x_787_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_736_, v_arg_729_, v_polarity_697_, v___x_782_, v_f_698_, v_a_699_);
return v___x_787_;
}
}
else
{
lean_object* v___x_788_; 
lean_dec_ref(v_arg_747_);
lean_dec_ref(v_e_693_);
v___x_788_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_736_, v_arg_729_, v_polarity_697_, v___x_743_, v_f_698_, v_a_699_);
return v___x_788_;
}
}
}
}
else
{
lean_dec_ref(v___x_737_);
lean_dec_ref(v_e_693_);
v_p_704_ = v_arg_736_;
v_q_705_ = v_arg_729_;
v___y_706_ = v_a_699_;
goto v___jp_703_;
}
}
else
{
lean_dec_ref(v___x_737_);
lean_dec_ref(v_e_693_);
v_p_704_ = v_arg_736_;
v_q_705_ = v_arg_729_;
v___y_706_ = v_a_699_;
goto v___jp_703_;
}
}
else
{
lean_object* v___x_789_; 
lean_dec_ref(v___x_737_);
lean_dec(v_toBind_700_);
lean_dec_ref(v_e_693_);
v___x_789_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_736_, v_arg_729_, v_polarity_697_, v___x_732_, v_f_698_, v_a_699_);
return v___x_789_;
}
}
}
else
{
lean_dec_ref(v___x_730_);
lean_dec(v_toBind_700_);
lean_dec_ref(v_e_693_);
if (v_polarity_697_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_729_, v___x_732_, v_f_698_, v_a_699_);
return v___x_790_;
}
else
{
uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_791_ = 0;
v___x_792_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_arg_729_, v___x_791_, v_f_698_, v_a_699_);
return v___x_792_;
}
}
}
}
v___jp_703_:
{
lean_object* v___x_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_707_ = lean_box(v_polarity_697_);
lean_inc(v___y_706_);
lean_inc(v_f_698_);
lean_inc(v_inst_696_);
lean_inc_ref(v_inst_694_);
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_708_, 0, v_inst_694_);
lean_closure_set(v___f_708_, 1, v_inst_695_);
lean_closure_set(v___f_708_, 2, v_inst_696_);
lean_closure_set(v___f_708_, 3, v_q_705_);
lean_closure_set(v___f_708_, 4, v___x_707_);
lean_closure_set(v___f_708_, 5, v_f_698_);
lean_closure_set(v___f_708_, 6, v___y_706_);
v___x_709_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_694_, v_inst_695_, v_inst_696_, v_p_704_, v_polarity_697_, v_f_698_, v___y_706_);
v___x_710_ = lean_apply_4(v_toBind_700_, lean_box(0), lean_box(0), v___x_709_, v___f_708_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___boxed(lean_object* v_e_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_polarity_797_, lean_object* v_f_798_, lean_object* v_a_799_, lean_object* v_toBind_800_, lean_object* v___x_801_, lean_object* v_a_802_){
_start:
{
uint8_t v_polarity_boxed_803_; lean_object* v_res_804_; 
v_polarity_boxed_803_ = lean_unbox(v_polarity_797_);
v_res_804_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8(v_e_793_, v_inst_794_, v_inst_795_, v_inst_796_, v_polarity_boxed_803_, v_f_798_, v_a_799_, v_toBind_800_, v___x_801_, v_a_802_);
lean_dec(v___x_801_);
lean_dec(v_a_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_e_808_, uint8_t v_polarity_809_, lean_object* v_f_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_812_; lean_object* v_toApplicative_813_; lean_object* v_toBind_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc_ref(v_inst_805_);
v___x_812_ = l_StateRefT_x27_instMonad___redArg(v_inst_805_);
v_toApplicative_813_ = lean_ctor_get(v_inst_805_, 0);
lean_inc_ref(v_toApplicative_813_);
v_toBind_814_ = lean_ctor_get(v_inst_805_, 1);
lean_inc_n(v_toBind_814_, 3);
v___x_815_ = lean_box(0);
v___x_816_ = l_instInhabitedOfMonad___redArg(v___x_812_, v___x_815_);
v___x_817_ = lean_box(v_polarity_809_);
lean_inc_n(v_a_811_, 3);
lean_inc_n(v_inst_807_, 2);
lean_inc_ref(v_e_808_);
v___f_818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_818_, 0, v_e_808_);
lean_closure_set(v___f_818_, 1, v_inst_805_);
lean_closure_set(v___f_818_, 2, v_inst_806_);
lean_closure_set(v___f_818_, 3, v_inst_807_);
lean_closure_set(v___f_818_, 4, v___x_817_);
lean_closure_set(v___f_818_, 5, v_f_810_);
lean_closure_set(v___f_818_, 6, v_a_811_);
lean_closure_set(v___f_818_, 7, v_toBind_814_);
lean_closure_set(v___f_818_, 8, v___x_816_);
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0));
v___f_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3));
v___x_821_ = lean_box(v_polarity_809_);
v___f_822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_822_, 0, v___x_819_);
lean_closure_set(v___f_822_, 1, v_e_808_);
lean_closure_set(v___f_822_, 2, v___x_821_);
lean_closure_set(v___f_822_, 3, v___f_820_);
lean_closure_set(v___f_822_, 4, v_a_811_);
lean_closure_set(v___f_822_, 5, v_inst_807_);
lean_closure_set(v___f_822_, 6, v_toBind_814_);
lean_closure_set(v___f_822_, 7, v___f_818_);
lean_closure_set(v___f_822_, 8, v_toApplicative_813_);
v___x_823_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_823_, 0, lean_box(0));
lean_closure_set(v___x_823_, 1, lean_box(0));
lean_closure_set(v___x_823_, 2, v_a_811_);
v___x_824_ = lean_apply_2(v_inst_807_, lean_box(0), v___x_823_);
v___x_825_ = lean_apply_4(v_toBind_814_, lean_box(0), lean_box(0), v___x_824_, v___f_822_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5(lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_arg_829_, uint8_t v___x_830_, lean_object* v_f_831_, lean_object* v_a_832_, lean_object* v_toBind_833_, lean_object* v___f_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_826_, v_inst_827_, v_inst_828_, v_arg_829_, v___x_830_, v_f_831_, v_a_832_);
v___x_837_ = lean_apply_4(v_toBind_833_, lean_box(0), lean_box(0), v___x_836_, v___f_834_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5___boxed(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_arg_841_, lean_object* v___x_842_, lean_object* v_f_843_, lean_object* v_a_844_, lean_object* v_toBind_845_, lean_object* v___f_846_, lean_object* v_a_847_){
_start:
{
uint8_t v___x_3602__boxed_848_; lean_object* v_res_849_; 
v___x_3602__boxed_848_ = lean_unbox(v___x_842_);
v_res_849_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5(v_inst_838_, v_inst_839_, v_inst_840_, v_arg_841_, v___x_3602__boxed_848_, v_f_843_, v_a_844_, v_toBind_845_, v___f_846_, v_a_847_);
lean_dec(v_a_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6(uint8_t v___x_850_, lean_object* v___x_851_, lean_object* v___x_852_, lean_object* v_f_853_, lean_object* v_e_854_, uint8_t v_polarity_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_a_859_, lean_object* v_toBind_860_, lean_object* v___f_861_, lean_object* v___f_862_, lean_object* v_a_863_){
_start:
{
if (v___x_850_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___closed__0));
lean_inc_ref(v___x_851_);
v___x_865_ = l_Lean_Name_mkStr2(v___x_851_, v___x_864_);
v___x_866_ = l_Lean_Expr_isConstOf(v___x_852_, v___x_865_);
lean_dec(v___x_865_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
lean_dec(v___f_862_);
v___x_867_ = l_Lean_Expr_isApp(v___x_852_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v___x_852_);
lean_dec_ref(v___x_851_);
v___x_868_ = lean_box(v_polarity_855_);
v___x_869_ = lean_apply_2(v_f_853_, v_e_854_, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v_arg_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_arg_870_ = lean_ctor_get(v___x_852_, 1);
lean_inc_ref(v_arg_870_);
v___x_871_ = l_Lean_Expr_appFnCleanup___redArg(v___x_852_);
lean_dec_ref(v___x_852_);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__0));
lean_inc_ref(v___x_851_);
v___x_873_ = l_Lean_Name_mkStr2(v___x_851_, v___x_872_);
v___x_874_ = l_Lean_Expr_isConstOf(v___x_871_, v___x_873_);
lean_dec(v___x_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Expr_isApp(v___x_871_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec_ref(v___x_871_);
lean_dec_ref(v_arg_870_);
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v___x_851_);
v___x_876_ = lean_box(v_polarity_855_);
v___x_877_ = lean_apply_2(v_f_853_, v_e_854_, v___x_876_);
return v___x_877_;
}
else
{
lean_object* v_arg_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_arg_878_ = lean_ctor_get(v___x_871_, 1);
lean_inc_ref(v_arg_878_);
v___x_879_ = l_Lean_Expr_appFnCleanup___redArg(v___x_871_);
lean_dec_ref(v___x_871_);
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__3));
v___x_881_ = l_Lean_Expr_isConstOf(v___x_879_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__4));
lean_inc_ref(v___x_851_);
v___x_883_ = l_Lean_Name_mkStr2(v___x_851_, v___x_882_);
v___x_884_ = l_Lean_Expr_isConstOf(v___x_879_, v___x_883_);
lean_dec(v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__5));
lean_inc_ref(v___x_851_);
v___x_886_ = l_Lean_Name_mkStr2(v___x_851_, v___x_885_);
v___x_887_ = l_Lean_Expr_isConstOf(v___x_879_, v___x_886_);
lean_dec(v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__6));
lean_inc_ref(v___x_851_);
v___x_889_ = l_Lean_Name_mkStr2(v___x_851_, v___x_888_);
v___x_890_ = l_Lean_Expr_isConstOf(v___x_879_, v___x_889_);
lean_dec(v___x_889_);
if (v___x_890_ == 0)
{
uint8_t v___x_891_; 
lean_dec(v___f_861_);
v___x_891_ = l_Lean_Expr_isApp(v___x_879_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v___x_879_);
lean_dec_ref(v_arg_878_);
lean_dec_ref(v_arg_870_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v___x_851_);
v___x_892_ = lean_box(v_polarity_855_);
v___x_893_ = lean_apply_2(v_f_853_, v_e_854_, v___x_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = l_Lean_Expr_appFnCleanup___redArg(v___x_879_);
v___x_895_ = l_Lean_Expr_isApp(v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v___x_894_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_arg_878_);
lean_dec_ref(v_arg_870_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v___x_851_);
v___x_896_ = lean_box(v_polarity_855_);
v___x_897_ = lean_apply_2(v_f_853_, v_e_854_, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_894_);
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__8));
v___x_900_ = l_Lean_Expr_isConstOf(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v_arg_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
lean_dec_ref(v___x_879_);
v_arg_901_ = lean_ctor_get(v___x_894_, 1);
lean_inc_ref(v_arg_901_);
lean_dec_ref(v___x_894_);
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__11));
v___x_903_ = l_Lean_Expr_isConstOf(v___x_898_, v___x_902_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
lean_dec_ref(v___x_851_);
v___x_904_ = l_Lean_Expr_isApp(v___x_898_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_arg_901_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v_arg_878_);
lean_dec_ref(v_arg_870_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
v___x_905_ = lean_box(v_polarity_855_);
v___x_906_ = lean_apply_2(v_f_853_, v_e_854_, v___x_905_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_898_);
lean_dec_ref(v___x_898_);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___closed__13));
v___x_909_ = l_Lean_Expr_isConstOf(v___x_907_, v___x_908_);
lean_dec_ref(v___x_907_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref(v_arg_901_);
lean_dec_ref(v_arg_878_);
lean_dec_ref(v_arg_870_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
v___x_910_ = lean_box(v_polarity_855_);
v___x_911_ = lean_apply_2(v_f_853_, v_e_854_, v___x_910_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___f_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_e_854_);
v___x_912_ = lean_box(v_polarity_855_);
lean_inc_n(v_a_859_, 3);
lean_inc_n(v_f_853_, 3);
lean_inc_n(v_inst_858_, 3);
lean_inc_ref_n(v_inst_856_, 3);
v___f_913_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_913_, 0, v_inst_856_);
lean_closure_set(v___f_913_, 1, v_inst_857_);
lean_closure_set(v___f_913_, 2, v_inst_858_);
lean_closure_set(v___f_913_, 3, v_arg_870_);
lean_closure_set(v___f_913_, 4, v___x_912_);
lean_closure_set(v___f_913_, 5, v_f_853_);
lean_closure_set(v___f_913_, 6, v_a_859_);
v___x_914_ = lean_box(v_polarity_855_);
lean_inc_n(v_toBind_860_, 2);
v___f_915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_915_, 0, v_inst_856_);
lean_closure_set(v___f_915_, 1, v_inst_857_);
lean_closure_set(v___f_915_, 2, v_inst_858_);
lean_closure_set(v___f_915_, 3, v_arg_878_);
lean_closure_set(v___f_915_, 4, v___x_914_);
lean_closure_set(v___f_915_, 5, v_f_853_);
lean_closure_set(v___f_915_, 6, v_a_859_);
lean_closure_set(v___f_915_, 7, v_toBind_860_);
lean_closure_set(v___f_915_, 8, v___f_913_);
v___x_916_ = lean_box(v___x_903_);
lean_inc_ref(v_arg_901_);
v___f_917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_917_, 0, v_inst_856_);
lean_closure_set(v___f_917_, 1, v_inst_857_);
lean_closure_set(v___f_917_, 2, v_inst_858_);
lean_closure_set(v___f_917_, 3, v_arg_901_);
lean_closure_set(v___f_917_, 4, v___x_916_);
lean_closure_set(v___f_917_, 5, v_f_853_);
lean_closure_set(v___f_917_, 6, v_a_859_);
lean_closure_set(v___f_917_, 7, v_toBind_860_);
lean_closure_set(v___f_917_, 8, v___f_915_);
v___x_918_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_901_, v___x_909_, v_f_853_, v_a_859_);
v___x_919_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_918_, v___f_917_);
return v___x_919_;
}
}
}
else
{
lean_object* v___x_920_; uint8_t v___x_921_; 
lean_dec_ref(v___x_898_);
lean_dec(v_toBind_860_);
v___x_920_ = l_Lean_Name_mkStr1(v___x_851_);
v___x_921_ = l_Lean_Expr_isConstOf(v_arg_901_, v___x_920_);
lean_dec(v___x_920_);
lean_dec_ref(v_arg_901_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v_arg_878_);
lean_dec_ref(v_arg_870_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
v___x_922_ = lean_box(v_polarity_855_);
v___x_923_ = lean_apply_2(v_f_853_, v_e_854_, v___x_922_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
lean_dec_ref(v_e_854_);
v___x_924_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_878_, v_arg_870_, v_polarity_855_, v___x_900_, v_f_853_, v_a_859_);
return v___x_924_;
}
}
}
else
{
lean_object* v_arg_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v_e_854_);
lean_dec_ref(v___x_851_);
v_arg_925_ = lean_ctor_get(v___x_879_, 1);
lean_inc_ref_n(v_arg_925_, 2);
lean_dec_ref(v___x_879_);
v___x_926_ = lean_box(v_polarity_855_);
lean_inc_n(v_a_859_, 3);
lean_inc_n(v_f_853_, 3);
lean_inc_n(v_inst_858_, 3);
lean_inc_ref_n(v_inst_856_, 3);
v___f_927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_927_, 0, v_inst_856_);
lean_closure_set(v___f_927_, 1, v_inst_857_);
lean_closure_set(v___f_927_, 2, v_inst_858_);
lean_closure_set(v___f_927_, 3, v_arg_870_);
lean_closure_set(v___f_927_, 4, v___x_926_);
lean_closure_set(v___f_927_, 5, v_f_853_);
lean_closure_set(v___f_927_, 6, v_a_859_);
v___x_928_ = lean_box(v_polarity_855_);
lean_inc_n(v_toBind_860_, 2);
v___f_929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_929_, 0, v_inst_856_);
lean_closure_set(v___f_929_, 1, v_inst_857_);
lean_closure_set(v___f_929_, 2, v_inst_858_);
lean_closure_set(v___f_929_, 3, v_arg_878_);
lean_closure_set(v___f_929_, 4, v___x_928_);
lean_closure_set(v___f_929_, 5, v_f_853_);
lean_closure_set(v___f_929_, 6, v_a_859_);
lean_closure_set(v___f_929_, 7, v_toBind_860_);
lean_closure_set(v___f_929_, 8, v___f_927_);
v___x_930_ = lean_box(v___x_890_);
v___f_931_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__8___boxed), 10, 9);
lean_closure_set(v___f_931_, 0, v_inst_856_);
lean_closure_set(v___f_931_, 1, v_inst_857_);
lean_closure_set(v___f_931_, 2, v_inst_858_);
lean_closure_set(v___f_931_, 3, v_arg_925_);
lean_closure_set(v___f_931_, 4, v___x_930_);
lean_closure_set(v___f_931_, 5, v_f_853_);
lean_closure_set(v___f_931_, 6, v_a_859_);
lean_closure_set(v___f_931_, 7, v_toBind_860_);
lean_closure_set(v___f_931_, 8, v___f_929_);
v___x_932_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_925_, v___x_900_, v_f_853_, v_a_859_);
v___x_933_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_932_, v___f_931_);
return v___x_933_;
}
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v___x_879_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v_e_854_);
lean_dec(v_f_853_);
lean_dec_ref(v___x_851_);
lean_inc(v_a_859_);
v___x_934_ = lean_apply_3(v___f_861_, v_arg_878_, v_arg_870_, v_a_859_);
return v___x_934_;
}
}
else
{
lean_object* v___x_935_; 
lean_dec_ref(v___x_879_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v_e_854_);
lean_dec(v_f_853_);
lean_dec_ref(v___x_851_);
lean_inc(v_a_859_);
v___x_935_ = lean_apply_3(v___f_861_, v_arg_878_, v_arg_870_, v_a_859_);
return v___x_935_;
}
}
else
{
lean_object* v___x_936_; 
lean_dec_ref(v___x_879_);
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec_ref(v_e_854_);
lean_dec_ref(v___x_851_);
v___x_936_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_878_, v_arg_870_, v_polarity_855_, v___x_884_, v_f_853_, v_a_859_);
return v___x_936_;
}
}
else
{
lean_object* v___x_937_; 
lean_dec_ref(v___x_879_);
lean_dec_ref(v_arg_870_);
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec_ref(v_e_854_);
lean_dec_ref(v___x_851_);
v___x_937_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_878_, v_polarity_855_, v_f_853_, v_a_859_);
return v___x_937_;
}
}
}
else
{
lean_dec_ref(v___x_871_);
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec_ref(v_e_854_);
lean_dec_ref(v___x_851_);
if (v_polarity_855_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_870_, v___x_874_, v_f_853_, v_a_859_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_856_, v_inst_857_, v_inst_858_, v_arg_870_, v___x_866_, v_f_853_, v_a_859_);
return v___x_939_;
}
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v_e_854_);
lean_dec(v_f_853_);
lean_dec_ref(v___x_852_);
lean_dec_ref(v___x_851_);
v___x_940_ = lean_box(0);
lean_inc(v_a_859_);
v___x_941_ = lean_apply_2(v___f_862_, v___x_940_, v_a_859_);
return v___x_941_;
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec(v_inst_858_);
lean_dec_ref(v_inst_856_);
lean_dec_ref(v_e_854_);
lean_dec(v_f_853_);
lean_dec_ref(v___x_852_);
lean_dec_ref(v___x_851_);
v___x_942_ = lean_box(0);
lean_inc(v_a_859_);
v___x_943_ = lean_apply_2(v___f_862_, v___x_942_, v_a_859_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___boxed(lean_object* v___x_944_, lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v_f_947_, lean_object* v_e_948_, lean_object* v_polarity_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_a_953_, lean_object* v_toBind_954_, lean_object* v___f_955_, lean_object* v___f_956_, lean_object* v_a_957_){
_start:
{
uint8_t v___x_3800__boxed_958_; uint8_t v_polarity_boxed_959_; lean_object* v_res_960_; 
v___x_3800__boxed_958_ = lean_unbox(v___x_944_);
v_polarity_boxed_959_ = lean_unbox(v_polarity_949_);
v_res_960_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6(v___x_3800__boxed_958_, v___x_945_, v___x_946_, v_f_947_, v_e_948_, v_polarity_boxed_959_, v_inst_950_, v_inst_951_, v_inst_952_, v_a_953_, v_toBind_954_, v___f_955_, v___f_956_, v_a_957_);
lean_dec(v_a_953_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_e_964_, uint8_t v_polarity_965_, lean_object* v_f_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_toApplicative_968_; lean_object* v_toBind_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___f_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___x_982_; lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_toApplicative_968_ = lean_ctor_get(v_inst_961_, 0);
lean_inc_ref_n(v_toApplicative_968_, 2);
v_toBind_969_ = lean_ctor_get(v_inst_961_, 1);
lean_inc_n(v_toBind_969_, 4);
v___x_970_ = lean_box(v_polarity_965_);
lean_inc(v_f_966_);
lean_inc_n(v_inst_963_, 3);
lean_inc_ref(v_inst_961_);
v___f_971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__1___boxed), 9, 6);
lean_closure_set(v___f_971_, 0, v_inst_961_);
lean_closure_set(v___f_971_, 1, v_inst_962_);
lean_closure_set(v___f_971_, 2, v_inst_963_);
lean_closure_set(v___f_971_, 3, v___x_970_);
lean_closure_set(v___f_971_, 4, v_f_966_);
lean_closure_set(v___f_971_, 5, v_toBind_969_);
v___f_972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_972_, 0, v_toApplicative_968_);
v___x_973_ = l_Lean_Expr_cleanupAnnotations(v_e_964_);
v___x_974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__0));
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___closed__2));
v___x_976_ = l_Lean_Expr_isConstOf(v___x_973_, v___x_975_);
v___x_977_ = lean_box(v___x_976_);
v___x_978_ = lean_box(v_polarity_965_);
lean_inc_n(v_a_967_, 3);
lean_inc_ref(v_e_964_);
v___f_979_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__6___boxed), 14, 13);
lean_closure_set(v___f_979_, 0, v___x_977_);
lean_closure_set(v___f_979_, 1, v___x_974_);
lean_closure_set(v___f_979_, 2, v___x_973_);
lean_closure_set(v___f_979_, 3, v_f_966_);
lean_closure_set(v___f_979_, 4, v_e_964_);
lean_closure_set(v___f_979_, 5, v___x_978_);
lean_closure_set(v___f_979_, 6, v_inst_961_);
lean_closure_set(v___f_979_, 7, v_inst_962_);
lean_closure_set(v___f_979_, 8, v_inst_963_);
lean_closure_set(v___f_979_, 9, v_a_967_);
lean_closure_set(v___f_979_, 10, v_toBind_969_);
lean_closure_set(v___f_979_, 11, v___f_971_);
lean_closure_set(v___f_979_, 12, v___f_972_);
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__0));
v___f_981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_withCheckCache___redArg___closed__3));
v___x_982_ = lean_box(v_polarity_965_);
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_983_, 0, v___x_980_);
lean_closure_set(v___f_983_, 1, v_e_964_);
lean_closure_set(v___f_983_, 2, v___x_982_);
lean_closure_set(v___f_983_, 3, v___f_981_);
lean_closure_set(v___f_983_, 4, v_a_967_);
lean_closure_set(v___f_983_, 5, v_inst_963_);
lean_closure_set(v___f_983_, 6, v_toBind_969_);
lean_closure_set(v___f_983_, 7, v___f_979_);
lean_closure_set(v___f_983_, 8, v_toApplicative_968_);
v___x_984_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_984_, 0, lean_box(0));
lean_closure_set(v___x_984_, 1, lean_box(0));
lean_closure_set(v___x_984_, 2, v_a_967_);
v___x_985_ = lean_apply_2(v_inst_963_, lean_box(0), v___x_984_);
v___x_986_ = lean_apply_4(v_toBind_969_, lean_box(0), lean_box(0), v___x_985_, v___f_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___lam__0(lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_q_990_, uint8_t v_polarity_991_, lean_object* v_f_992_, lean_object* v___y_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_987_, v_inst_988_, v_inst_989_, v_q_990_, v_polarity_991_, v_f_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg___boxed(lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_e_999_, lean_object* v_polarity_1000_, lean_object* v_f_1001_, lean_object* v_a_1002_){
_start:
{
uint8_t v_polarity_boxed_1003_; lean_object* v_res_1004_; 
v_polarity_boxed_1003_ = lean_unbox(v_polarity_1000_);
v_res_1004_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_996_, v_inst_997_, v_inst_998_, v_e_999_, v_polarity_boxed_1003_, v_f_1001_, v_a_1002_);
lean_dec(v_a_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg___boxed(lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_e_1008_, lean_object* v_polarity_1009_, lean_object* v_f_1010_, lean_object* v_a_1011_){
_start:
{
uint8_t v_polarity_boxed_1012_; lean_object* v_res_1013_; 
v_polarity_boxed_1012_ = lean_unbox(v_polarity_1009_);
v_res_1013_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_1005_, v_inst_1006_, v_inst_1007_, v_e_1008_, v_polarity_boxed_1012_, v_f_1010_, v_a_1011_);
lean_dec(v_a_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg___boxed(lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_p_1017_, lean_object* v_q_1018_, lean_object* v_polarity_1019_, lean_object* v_flip_1020_, lean_object* v_f_1021_, lean_object* v_a_1022_){
_start:
{
uint8_t v_polarity_boxed_1023_; uint8_t v_flip_boxed_1024_; lean_object* v_res_1025_; 
v_polarity_boxed_1023_ = lean_unbox(v_polarity_1019_);
v_flip_boxed_1024_ = lean_unbox(v_flip_1020_);
v_res_1025_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg(v_inst_1014_, v_inst_1015_, v_inst_1016_, v_p_1017_, v_q_1018_, v_polarity_boxed_1023_, v_flip_boxed_1024_, v_f_1021_, v_a_1022_);
lean_dec(v_a_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg___boxed(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_inst_1028_, lean_object* v_p_1029_, lean_object* v_q_1030_, lean_object* v_polarity_1031_, lean_object* v_flip_1032_, lean_object* v_f_1033_, lean_object* v_a_1034_){
_start:
{
uint8_t v_polarity_boxed_1035_; uint8_t v_flip_boxed_1036_; lean_object* v_res_1037_; 
v_polarity_boxed_1035_ = lean_unbox(v_polarity_1031_);
v_flip_boxed_1036_ = lean_unbox(v_flip_1032_);
v_res_1037_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(v_inst_1026_, v_inst_1027_, v_inst_1028_, v_p_1029_, v_q_1030_, v_polarity_boxed_1035_, v_flip_boxed_1036_, v_f_1033_, v_a_1034_);
lean_dec(v_a_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth(lean_object* v_m_1038_, lean_object* v_inst_1039_, lean_object* v_00_u03c3_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_p_1043_, lean_object* v_q_1044_, uint8_t v_polarity_1045_, uint8_t v_flip_1046_, lean_object* v_f_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___redArg(v_inst_1039_, v_inst_1041_, v_inst_1042_, v_p_1043_, v_q_1044_, v_polarity_1045_, v_flip_1046_, v_f_1047_, v_a_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth___boxed(lean_object* v_m_1050_, lean_object* v_inst_1051_, lean_object* v_00_u03c3_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_p_1055_, lean_object* v_q_1056_, lean_object* v_polarity_1057_, lean_object* v_flip_1058_, lean_object* v_f_1059_, lean_object* v_a_1060_){
_start:
{
uint8_t v_polarity_boxed_1061_; uint8_t v_flip_boxed_1062_; lean_object* v_res_1063_; 
v_polarity_boxed_1061_ = lean_unbox(v_polarity_1057_);
v_flip_boxed_1062_ = lean_unbox(v_flip_1058_);
v_res_1063_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27_visitBoth(v_m_1050_, v_inst_1051_, v_00_u03c3_1052_, v_inst_1053_, v_inst_1054_, v_p_1055_, v_q_1056_, v_polarity_boxed_1061_, v_flip_boxed_1062_, v_f_1059_, v_a_1060_);
lean_dec(v_a_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27(lean_object* v_m_1064_, lean_object* v_inst_1065_, lean_object* v_00_u03c3_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_e_1069_, uint8_t v_polarity_1070_, lean_object* v_f_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_1065_, v_inst_1067_, v_inst_1068_, v_e_1069_, v_polarity_1070_, v_f_1071_, v_a_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___boxed(lean_object* v_m_1074_, lean_object* v_inst_1075_, lean_object* v_00_u03c3_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_e_1079_, lean_object* v_polarity_1080_, lean_object* v_f_1081_, lean_object* v_a_1082_){
_start:
{
uint8_t v_polarity_boxed_1083_; lean_object* v_res_1084_; 
v_polarity_boxed_1083_ = lean_unbox(v_polarity_1080_);
v_res_1084_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27(v_m_1074_, v_inst_1075_, v_00_u03c3_1076_, v_inst_1077_, v_inst_1078_, v_e_1079_, v_polarity_boxed_1083_, v_f_1081_, v_a_1082_);
lean_dec(v_a_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27(lean_object* v_m_1085_, lean_object* v_inst_1086_, lean_object* v_00_u03c3_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_e_1090_, uint8_t v_polarity_1091_, lean_object* v_f_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___redArg(v_inst_1086_, v_inst_1088_, v_inst_1089_, v_e_1090_, v_polarity_1091_, v_f_1092_, v_a_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___boxed(lean_object* v_m_1095_, lean_object* v_inst_1096_, lean_object* v_00_u03c3_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_e_1100_, lean_object* v_polarity_1101_, lean_object* v_f_1102_, lean_object* v_a_1103_){
_start:
{
uint8_t v_polarity_boxed_1104_; lean_object* v_res_1105_; 
v_polarity_boxed_1104_ = lean_unbox(v_polarity_1101_);
v_res_1105_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27(v_m_1095_, v_inst_1096_, v_00_u03c3_1097_, v_inst_1098_, v_inst_1099_, v_e_1100_, v_polarity_boxed_1104_, v_f_1102_, v_a_1103_);
lean_dec(v_a_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth(lean_object* v_m_1106_, lean_object* v_inst_1107_, lean_object* v_00_u03c3_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_p_1111_, lean_object* v_q_1112_, uint8_t v_polarity_1113_, uint8_t v_flip_1114_, lean_object* v_f_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___redArg(v_inst_1107_, v_inst_1109_, v_inst_1110_, v_p_1111_, v_q_1112_, v_polarity_1113_, v_flip_1114_, v_f_1115_, v_a_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth___boxed(lean_object* v_m_1118_, lean_object* v_inst_1119_, lean_object* v_00_u03c3_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_p_1123_, lean_object* v_q_1124_, lean_object* v_polarity_1125_, lean_object* v_flip_1126_, lean_object* v_f_1127_, lean_object* v_a_1128_){
_start:
{
uint8_t v_polarity_boxed_1129_; uint8_t v_flip_boxed_1130_; lean_object* v_res_1131_; 
v_polarity_boxed_1129_ = lean_unbox(v_polarity_1125_);
v_flip_boxed_1130_ = lean_unbox(v_flip_1126_);
v_res_1131_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27_visitBoth(v_m_1118_, v_inst_1119_, v_00_u03c3_1120_, v_inst_1121_, v_inst_1122_, v_p_1123_, v_q_1124_, v_polarity_boxed_1129_, v_flip_boxed_1130_, v_f_1127_, v_a_1128_);
lean_dec(v_a_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp___redArg(lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_e_1135_, lean_object* v_f_1136_){
_start:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = 1;
v___x_1138_ = lean_box(v___x_1137_);
lean_inc(v_inst_1134_);
lean_inc_ref(v_inst_1132_);
v___x_1139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp_x27___boxed), 9, 8);
lean_closure_set(v___x_1139_, 0, lean_box(0));
lean_closure_set(v___x_1139_, 1, v_inst_1132_);
lean_closure_set(v___x_1139_, 2, lean_box(0));
lean_closure_set(v___x_1139_, 3, v_inst_1133_);
lean_closure_set(v___x_1139_, 4, v_inst_1134_);
lean_closure_set(v___x_1139_, 5, v_e_1135_);
lean_closure_set(v___x_1139_, 6, v___x_1138_);
lean_closure_set(v___x_1139_, 7, v_f_1136_);
v___x_1140_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg(v_inst_1132_, v_inst_1134_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp(lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_00_u03c3_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_e_1146_, lean_object* v_f_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitProp___redArg(v_inst_1142_, v_inst_1144_, v_inst_1145_, v_e_1146_, v_f_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__0(lean_object* v_a_1149_, lean_object* v_toPure_1150_, lean_object* v_s_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_a_1149_);
lean_ctor_set(v___x_1152_, 1, v_s_1151_);
v___x_1153_ = lean_apply_2(v_toPure_1150_, lean_box(0), v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__1(lean_object* v_toPure_1154_, lean_object* v_ref_1155_, lean_object* v_inst_1156_, lean_object* v_toBind_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___f_1159_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1159_, 0, v_a_1158_);
lean_closure_set(v___f_1159_, 1, v_toPure_1154_);
v___x_1160_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1160_, 0, lean_box(0));
lean_closure_set(v___x_1160_, 1, lean_box(0));
lean_closure_set(v___x_1160_, 2, v_ref_1155_);
v___x_1161_ = lean_apply_2(v_inst_1156_, lean_box(0), v___x_1160_);
v___x_1162_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1161_, v___f_1159_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__2(lean_object* v_toPure_1163_, lean_object* v_inst_1164_, lean_object* v_toBind_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_e_1168_, uint8_t v___x_1169_, lean_object* v_f_1170_, lean_object* v_ref_1171_){
_start:
{
lean_object* v___f_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc(v_toBind_1165_);
lean_inc(v_inst_1164_);
lean_inc(v_ref_1171_);
v___f_1172_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1172_, 0, v_toPure_1163_);
lean_closure_set(v___f_1172_, 1, v_ref_1171_);
lean_closure_set(v___f_1172_, 2, v_inst_1164_);
lean_closure_set(v___f_1172_, 3, v_toBind_1165_);
v___x_1173_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool_x27___redArg(v_inst_1166_, v_inst_1167_, v_inst_1164_, v_e_1168_, v___x_1169_, v_f_1170_, v_ref_1171_);
lean_dec(v_ref_1171_);
v___x_1174_ = lean_apply_4(v_toBind_1165_, lean_box(0), lean_box(0), v___x_1173_, v___f_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__2___boxed(lean_object* v_toPure_1175_, lean_object* v_inst_1176_, lean_object* v_toBind_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_e_1180_, lean_object* v___x_1181_, lean_object* v_f_1182_, lean_object* v_ref_1183_){
_start:
{
uint8_t v___x_99__boxed_1184_; lean_object* v_res_1185_; 
v___x_99__boxed_1184_ = lean_unbox(v___x_1181_);
v_res_1185_ = l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__2(v_toPure_1175_, v_inst_1176_, v_toBind_1177_, v_inst_1178_, v_inst_1179_, v_e_1180_, v___x_99__boxed_1184_, v_f_1182_, v_ref_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__3(lean_object* v_toPure_1186_, lean_object* v_____x_1187_){
_start:
{
lean_object* v_fst_1188_; lean_object* v___x_1189_; 
v_fst_1188_ = lean_ctor_get(v_____x_1187_, 0);
lean_inc(v_fst_1188_);
lean_dec_ref(v_____x_1187_);
v___x_1189_ = lean_apply_2(v_toPure_1186_, lean_box(0), v_fst_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg(lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_e_1193_, lean_object* v_f_1194_){
_start:
{
lean_object* v_toApplicative_1195_; lean_object* v_toBind_1196_; lean_object* v_toPure_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_toApplicative_1195_ = lean_ctor_get(v_inst_1190_, 0);
v_toBind_1196_ = lean_ctor_get(v_inst_1190_, 1);
lean_inc_n(v_toBind_1196_, 3);
v_toPure_1197_ = lean_ctor_get(v_toApplicative_1195_, 1);
lean_inc_n(v_toPure_1197_, 2);
v___x_1198_ = 1;
v___x_1199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_0__Lean_Meta_Tactic_BVDecide_EPR_VisitM_run___redArg___closed__2);
lean_inc(v_inst_1192_);
v___x_1200_ = lean_apply_2(v_inst_1192_, lean_box(0), v___x_1199_);
v___x_1201_ = lean_box(v___x_1198_);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1202_, 0, v_toPure_1197_);
lean_closure_set(v___f_1202_, 1, v_inst_1192_);
lean_closure_set(v___f_1202_, 2, v_toBind_1196_);
lean_closure_set(v___f_1202_, 3, v_inst_1190_);
lean_closure_set(v___f_1202_, 4, v_inst_1191_);
lean_closure_set(v___f_1202_, 5, v_e_1193_);
lean_closure_set(v___f_1202_, 6, v___x_1201_);
lean_closure_set(v___f_1202_, 7, v_f_1194_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1203_, 0, v_toPure_1197_);
v___x_1204_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v___x_1200_, v___f_1202_);
v___x_1205_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v___x_1204_, v___f_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool(lean_object* v_m_1206_, lean_object* v_inst_1207_, lean_object* v_00_u03c3_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_e_1211_, lean_object* v_f_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor_visitBool___redArg(v_inst_1207_, v_inst_1209_, v_inst_1210_, v_e_1211_, v_f_1212_);
return v___x_1213_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_EPR_PolarityVisitor(builtin);
}
#ifdef __cplusplus
}
#endif
