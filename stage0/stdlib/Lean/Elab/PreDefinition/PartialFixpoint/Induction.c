// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Induction
// Imports: import Lean.Meta.Injective import Lean.Elab.PreDefinition.PartialFixpoint.Eqns import Init.Internal.Order.Basic import Lean.Meta.PProdN
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "admissible_and"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(254, 171, 253, 255, 31, 197, 49, 36)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "instCCPOPProd"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 223, 146, 139, 208, 109, 106, 240)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "mkAdmProj: unexpected instance "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__2_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "admissible_pprod_snd"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__4_value),LEAN_SCALAR_PTR_LITERAL(151, 90, 190, 201, 15, 167, 240, 87)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "admissible_pprod_fst"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__6_value),LEAN_SCALAR_PTR_LITERAL(236, 12, 82, 69, 179, 4, 227, 50)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Elab.PreDefinition.PartialFixpoint.Induction"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__8_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "_private.Lean.Elab.PreDefinition.PartialFixpoint.Induction.0.Lean.Elab.PartialFixpoint.mkAdmProj"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__9_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "assertion violation: i == 0\n    "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__10_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__11;
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs_spec__0(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Cannot apply lattice induction to a non-lattice fixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__1;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__1;
uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__4(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__7;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_projM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = " is not an application of partial order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "induction"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__6_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__7_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8_value),LEAN_SCALAR_PTR_LITERAL(152, 173, 218, 79, 164, 88, 9, 3)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "predTypes: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__11;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_PProdN_unpack___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg___closed__0_value;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___closed__0_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mutual_induct"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 83, 25, 196, 5, 111, 46, 167)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot get fixpoint type for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fixpoint_induct"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 250, 85, 43, 175, 125, 191, 192)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__5_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "mutual_fixpoint_induct"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6_value),LEAN_SCALAR_PTR_LITERAL(138, 14, 184, 65, 6, 159, 28, 191)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "coinduct"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__8_value),LEAN_SCALAR_PTR_LITERAL(65, 240, 113, 153, 84, 237, 79, 21)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__9_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__10 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__10_value),LEAN_SCALAR_PTR_LITERAL(157, 227, 157, 243, 169, 45, 185, 145)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__11_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = " is not defined by partial_fixpoint, inductive_fixpoint, nor coinductive_fixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__13;
extern lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
extern lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Unexpected function type "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = ", not an application of PartialOrder.rel"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__3;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__3(lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__1(lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Complete body of fixpoint induction principle:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hyp"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___closed__0_value;
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3(lean_object*, lean_object*, size_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___boxed(lean_object**);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_proj(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_projs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ih"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 60, 57, 160, 49, 55, 75, 124)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__1_value;
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__19;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0;
extern lean_object* l_Lean_instInhabitedDefinitionVal_default;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "approx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 7, 73, 97, 68, 25, 104, 39)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fix_induct"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "packedConclusion: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", index is: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__6;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__1___boxed(lean_object**);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__1;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed__const__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___closed__0_value;
lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___boxed(lean_object**);
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "admissible"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 149, 233, 132, 37, 111, 67, 182)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "adm"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__2_value;
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___boxed(lean_object**);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__9(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Unexpected function body "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ", not an application of lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = ", not an application of fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 115, 213, 20, 156, 86, 56, 31)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "lfp_le_of_le_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__8_value),LEAN_SCALAR_PTR_LITERAL(79, 119, 83, 117, 75, 189, 70, 86)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pred"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__11_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = ", could not whnfUntil lfp_monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__12 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__13;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__14_value),LEAN_SCALAR_PTR_LITERAL(18, 104, 23, 57, 110, 104, 99, 16)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__16 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__16_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ", could not whnfUntil fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__17 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__18;
lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24_spec__29(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__1;
static const lean_array_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eTyp last: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = " is not defined by partial_fixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7;
lean_object* l_Lean_Meta_elimOptParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__12(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "Cannot derive fixpoint induction principle (please report this issue)"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Called deriveInduction for "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__4;
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__6_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__7_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0_value;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__1(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_isPartialFixpoint(uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isInductiveFixpoint(uint8_t);
uint8_t l_Lean_Elab_isCoinductiveFixpoint(uint8_t);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_;
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__value;
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_private.Lean.Elab.PreDefinition.PartialFixpoint.Induction.0.Lean.Elab.PartialFixpoint.isOptionFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "isOptionFixpoint: unexpected value "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__1_value;
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instCCPOPi"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 4, 22, 67, 25, 201, 243, 223)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1_value;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instCCPOOption"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 85, 181, 162, 5, 15, 174, 164)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__2(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: defnInfo.hasValue\n  "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "partial_correctness"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "mutual_partial_correctness"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "admissible_pi_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 111, 91, 234, 63, 187, 221, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__4;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "admissible_eq_some"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(131, 157, 117, 0, 224, 216, 87, 167)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 120, 80, 76, 248, 129, 76, 205)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "admissible_pi"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(81, 191, 147, 155, 106, 82, 73, 23)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4_value;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__1_value;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Expected `Option`, got:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__1;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "motive_"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__16_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "complete body of partial correctness principle:"};
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "Cannot derive partial correctness theorem (please report this issue)"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 124, 39, 217, 198, 168, 162, 152)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 187, 211, 101, 43, 192, 199, 162)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 13, 156, 207, 122, 14, 28, 133)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Induction"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 211, 207, 56, 17, 170, 237, 149)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(40, 217, 229, 84, 174, 135, 41, 169)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 177, 28, 163, 210, 193, 32, 179)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(184, 109, 93, 1, 159, 203, 191, 18)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 202, 43, 139, 34, 66, 119, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5_value),LEAN_SCALAR_PTR_LITERAL(143, 22, 129, 226, 29, 213, 56, 226)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 133, 157, 112, 180, 125, 148, 129)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 49, 40, 0, 130, 126, 144, 203)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 60, 247, 244, 213, 112, 227, 100)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)(((size_t)(486719255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 70, 220, 53, 140, 50, 84, 91)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 85, 238, 228, 76, 109, 141, 63)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 87, 151, 214, 66, 161, 203, 64)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(36, 77, 163, 115, 130, 146, 99, 137)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3));
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = lean_unsigned_to_nat(6u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_11);
x_19 = lean_array_push(x_18, x_12);
x_20 = lean_array_push(x_19, x_13);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_14);
x_23 = lean_array_push(x_22, x_15);
x_24 = l_Lean_Meta_mkAppOptM(x_10, x_23, x_5, x_6, x_7, x_8);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__10));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(33u);
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__9));
x_5 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__8));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = l_Lean_Meta_whnfUntil(x_1, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_98; 
x_11 = lean_ctor_get(x_10, 0);
x_98 = !lean_is_exclusive(x_10);
if (x_98 == 0)
{
x_12 = x_10;
x_13 = x_98;
goto block_97;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_98;
goto block_97;
}
block_97:
{
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_89; 
lean_del_object(x_12);
x_14 = lean_ctor_get(x_11, 0);
x_89 = !lean_is_exclusive(x_11);
if (x_89 == 0)
{
x_15 = x_11;
x_16 = x_89;
goto block_88;
}
else
{
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; uint8_t x_27; 
lean_inc(x_14);
x_26 = l_Lean_Expr_cleanupAnnotations(x_14);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_del_object(x_15);
lean_dec_ref(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_del_object(x_15);
lean_dec_ref(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_del_object(x_15);
lean_dec_ref(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_34);
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_del_object(x_15);
lean_dec_ref(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_25;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_37);
x_38 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_39 = l_Lean_Expr_isConstOf(x_38, x_9);
lean_dec_ref(x_38);
if (x_39 == 0)
{
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_del_object(x_15);
lean_dec_ref(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
goto block_25;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_14);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_2, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_2, x_42);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_28);
x_44 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj(x_28, x_43, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_69; 
x_45 = lean_ctor_get(x_44, 0);
x_69 = !lean_is_exclusive(x_44);
if (x_69 == 0)
{
x_46 = x_44;
x_47 = x_69;
goto block_68;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_48; lean_object* x_49; 
x_48 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__5));
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_37);
x_49 = x_15;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_37);
x_49 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_50; 
if (x_47 == 0)
{
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_34);
x_50 = x_46;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_34);
x_50 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_31);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_28);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_45);
x_55 = lean_unsigned_to_nat(6u);
x_56 = lean_mk_empty_array_with_capacity(x_55);
x_57 = lean_array_push(x_56, x_49);
x_58 = lean_array_push(x_57, x_50);
x_59 = lean_array_push(x_58, x_51);
x_60 = lean_array_push(x_59, x_52);
x_61 = lean_array_push(x_60, x_53);
x_62 = lean_array_push(x_61, x_54);
x_63 = l_Lean_Meta_mkAppOptM(x_48, x_62, x_4, x_5, x_6, x_7);
return x_63;
}
}
}
}
else
{
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec_ref(x_28);
lean_del_object(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_44;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__7));
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_37);
x_71 = x_15;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_37);
x_71 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_34);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_31);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_28);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_3);
x_77 = lean_unsigned_to_nat(6u);
x_78 = lean_mk_empty_array_with_capacity(x_77);
x_79 = lean_array_push(x_78, x_71);
x_80 = lean_array_push(x_79, x_72);
x_81 = lean_array_push(x_80, x_73);
x_82 = lean_array_push(x_81, x_74);
x_83 = lean_array_push(x_82, x_75);
x_84 = lean_array_push(x_83, x_76);
x_85 = l_Lean_Meta_mkAppOptM(x_70, x_84, x_4, x_5, x_6, x_7);
return x_85;
}
}
}
}
}
}
}
block_25:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__3);
x_22 = l_Lean_MessageData_ofExpr(x_14);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_23, x_17, x_18, x_19, x_20);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
return x_24;
}
}
}
else
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_11);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_dec_eq(x_2, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_del_object(x_12);
lean_dec_ref(x_3);
x_92 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__11);
x_93 = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__1(x_92, x_4, x_5, x_6, x_7);
return x_93;
}
else
{
lean_object* x_94; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_3);
x_94 = x_12;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_3);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_99 = lean_ctor_get(x_10, 0);
x_106 = !lean_is_exclusive(x_10);
if (x_106 == 0)
{
x_100 = x_10;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_10);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_instInhabitedExpr;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_array_get_borrowed(x_5, x_2, x_7);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_Expr_cleanupAnnotations(x_8);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec_ref(x_9);
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_12);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_12);
goto _start;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_12);
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__1));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_12);
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_array_pop(x_2);
x_28 = lean_array_push(x_27, x_16);
x_29 = lean_array_push(x_28, x_12);
x_2 = x_29;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_array_push(x_4, x_2);
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs_spec__0(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
x_13 = x_11;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_20 = lean_ctor_get(x_11, 0);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
x_21 = x_11;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_mkAppN(x_1, x_6);
x_14 = l_Lean_mkAppN(x_2, x_6);
if (x_5 == 0)
{
x_15 = x_13;
goto block_28;
}
else
{
lean_object* x_29; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_29 = lean_whnf(x_13, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_15 = x_30;
goto block_28;
}
else
{
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_29;
}
}
block_28:
{
switch (x_3) {
case 0:
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
x_16 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___closed__1);
x_17 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_16, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_17;
}
case 1:
{
lean_object* x_18; 
lean_inc(x_11);
lean_inc_ref(x_10);
x_18 = l_Lean_mkArrow(x_14, x_15, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 0;
x_21 = 1;
x_22 = l_Lean_Meta_mkForallFVars(x_6, x_19, x_20, x_4, x_4, x_21, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_22;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_18;
}
}
default: 
{
lean_object* x_23; 
lean_inc(x_11);
lean_inc_ref(x_10);
x_23 = l_Lean_mkArrow(x_15, x_14, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = 0;
x_26 = 1;
x_27 = l_Lean_Meta_mkForallFVars(x_6, x_24, x_25, x_4, x_4, x_26, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_27;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0(x_1, x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Elab_isLatticeTheoretic(x_4);
x_12 = 1;
x_13 = lean_box(x_4);
x_14 = lean_box(x_12);
x_15 = lean_box(x_5);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___lam__0___boxed), 12, 5);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
if (x_11 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_16);
lean_dec_ref(x_1);
x_20 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___closed__1);
x_21 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_20, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_22 = lean_ctor_get(x_21, 0);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
x_23 = x_21;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
goto block_19;
}
block_19:
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg(x_1, x_16, x_17, x_17, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_54; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
x_11 = x_9;
x_12 = x_54;
goto block_53;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_52; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
x_23 = x_13;
x_24 = x_52;
goto block_51;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_52;
goto block_51;
}
block_51:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_50; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
x_27 = x_14;
x_28 = x_50;
goto block_49;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_29; double x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_box(0);
x_30 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__0);
x_31 = 0;
x_32 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__1));
x_33 = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set_float(x_33, sizeof(void*)*3, x_30);
lean_ctor_set_float(x_33, sizeof(void*)*3 + 8, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*3 + 16, x_31);
x_34 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___closed__2));
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_10);
lean_ctor_set(x_35, 2, x_34);
lean_inc(x_8);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_PersistentArray_push___redArg(x_26, x_36);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_37);
x_38 = x_27;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set_uint64(x_48, sizeof(void*)*1, x_25);
x_38 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_39; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_38);
x_39 = x_23;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_16);
lean_ctor_set(x_46, 2, x_17);
lean_ctor_set(x_46, 3, x_18);
lean_ctor_set(x_46, 4, x_38);
lean_ctor_set(x_46, 5, x_19);
lean_ctor_set(x_46, 6, x_20);
lean_ctor_set(x_46, 7, x_21);
lean_ctor_set(x_46, 8, x_22);
x_39 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_st_ref_set(x_6, x_39);
x_41 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_41);
x_42 = x_11;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofExpr(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_70; 
x_7 = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0);
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
x_70 = !lean_is_exclusive(x_8);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_8, 1);
lean_dec(x_71);
x_10 = x_8;
x_11 = x_70;
goto block_69;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_67; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_67 = !lean_is_exclusive(x_9);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_9, 1);
lean_dec(x_68);
x_16 = x_9;
x_17 = x_67;
goto block_66;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__1));
x_19 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__2));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_22);
lean_ctor_set(x_65, 1, x_18);
lean_ctor_set(x_65, 2, x_25);
lean_ctor_set(x_65, 3, x_24);
lean_ctor_set(x_65, 4, x_23);
x_26 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_19);
x_27 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_60; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = lean_ctor_get(x_28, 0);
x_60 = !lean_is_exclusive(x_28);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_28, 1);
lean_dec(x_61);
x_30 = x_28;
x_31 = x_60;
goto block_59;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_57; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_57 = !lean_is_exclusive(x_29);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_29, 1);
lean_dec(x_58);
x_36 = x_29;
x_37 = x_57;
goto block_56;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__3));
x_39 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__4));
lean_inc_ref(x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_34);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_33);
if (x_37 == 0)
{
lean_ctor_set(x_36, 4, x_43);
lean_ctor_set(x_36, 3, x_44);
lean_ctor_set(x_36, 2, x_45);
lean_ctor_set(x_36, 1, x_38);
lean_ctor_set(x_36, 0, x_42);
x_46 = x_36;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_38);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_44);
lean_ctor_set(x_55, 4, x_43);
x_46 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_47; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_39);
lean_ctor_set(x_30, 0, x_46);
x_47 = x_30;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_39);
x_47 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_box(0);
x_49 = l_instInhabitedOfMonad___redArg(x_47, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_5(x_50, x_2, x_3, x_4, x_5, lean_box(0));
return x_51;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__6));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(115u);
x_4 = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__5));
x_5 = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_st_ref_get(x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_1);
x_18 = l_Lean_Environment_findAsync_x3f(x_16, x_1, x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_AsyncConstantInfo_toConstantInfo(x_19);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
x_23 = x_21;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_21);
x_30 = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_31 = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0(x_30, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_40; 
x_32 = lean_ctor_get(x_31, 0);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
x_33 = x_31;
x_34 = x_40;
goto block_39;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_40;
goto block_39;
}
block_39:
{
if (lean_obj_tag(x_32) == 0)
{
lean_del_object(x_33);
goto block_14;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_31, 0);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_42 = x_31;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
else
{
lean_dec(x_19);
goto block_14;
}
}
else
{
lean_dec(x_18);
goto block_14;
}
block_14:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1);
x_8 = 0;
x_9 = l_Lean_MessageData_ofConstName(x_1, x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__3);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_12, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_12 = l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_12, 0);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
x_21 = x_12;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_7, x_15);
if (x_16 == 1)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_34; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
lean_dec(x_7);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_2);
x_34 = l_Lean_Meta_PProdN_projM(x_1, x_8, x_2, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_36 = l_Lean_Meta_PProdN_reduceProjs(x_35, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_3);
x_38 = l_Lean_Meta_PProdN_projM(x_1, x_8, x_3, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_5, 7);
x_41 = l_Lean_instInhabitedExpr;
x_42 = 0;
x_43 = lean_array_get_borrowed(x_41, x_4, x_8);
x_44 = lean_box(x_42);
x_45 = lean_array_get_borrowed(x_44, x_40, x_8);
x_46 = lean_unbox(x_45);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_43);
x_47 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel(x_43, x_37, x_39, x_46, x_6, x_10, x_11, x_12, x_13);
x_20 = x_47;
goto block_33;
}
else
{
lean_dec(x_37);
x_20 = x_38;
goto block_33;
}
}
else
{
x_20 = x_36;
goto block_33;
}
}
else
{
x_20 = x_34;
goto block_33;
}
block_33:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_23 = lean_array_push(x_9, x_21);
x_7 = x_19;
x_8 = x_22;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_20, 0);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
x_26 = x_20;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_6);
x_16 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_2);
x_18 = l_Lean_Expr_cleanupAnnotations(x_2);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_1);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_1);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_1);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_17;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_1);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__4));
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
lean_dec_ref(x_29);
if (x_31 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_1);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_17;
}
else
{
lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec_ref(x_2);
x_32 = lean_ctor_get(x_1, 4);
x_33 = lean_array_size(x_32);
x_34 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_32);
x_35 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1(x_33, x_34, x_32, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = l_Lean_Meta_PProdN_unpack___redArg(x_28, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_48 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9));
x_49 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_48, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
goto block_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__11);
lean_inc(x_39);
x_53 = lean_array_to_list(x_39);
x_54 = lean_box(0);
x_55 = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__4(x_53, x_54);
x_56 = l_Lean_MessageData_ofList(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_48, x_57, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
goto block_47;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_39);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_58, 0);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
x_60 = x_58;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
block_47:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_mk_empty_array_with_capacity(x_37);
x_46 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg(x_37, x_23, x_20, x_39, x_1, x_3, x_37, x_44, x_45, x_40, x_41, x_42, x_43);
lean_dec_ref(x_1);
lean_dec(x_39);
return x_46;
}
}
else
{
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_38;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_28);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_35, 0);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
x_68 = x_35;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_35);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
}
}
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_MessageData_ofExpr(x_2);
x_14 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_15, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
x_18 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__2(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_45; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 0);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
x_13 = x_4;
x_14 = x_45;
goto block_44;
}
else
{
lean_inc(x_11);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
if (x_14 == 0)
{
x_19 = x_13;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_11);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_40; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_11, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_11, 0);
lean_dec(x_43);
x_22 = x_11;
x_23 = x_40;
goto block_39;
}
else
{
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_array_uget_borrowed(x_1, x_3);
x_25 = lean_array_fget(x_15, x_16);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_16, x_26);
lean_dec(x_16);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_27);
x_28 = x_22;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_17);
x_28 = x_38;
goto block_37;
}
block_37:
{
uint8_t x_29; 
x_29 = lean_unbox(x_24);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_25);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_28);
x_30 = x_13;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_28);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_5 = x_30;
goto block_9;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_push(x_12, x_25);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_33);
x_34 = x_13;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_28);
x_34 = x_36;
goto block_35;
}
block_35:
{
x_5 = x_34;
goto block_9;
}
}
}
}
}
}
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_3, x_6);
x_3 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg___closed__0));
x_5 = lean_array_get_size(x_2);
x_6 = l_Array_toSubarray___redArg(x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg(x_1, x_8, x_9, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___closed__0));
x_7 = lean_string_append(x_2, x_6);
x_8 = lean_nat_add(x_3, x_4);
x_9 = l_Nat_reprFast(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Name_str___override(x_11, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Name_str___override(x_13, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Array_ofFn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_findIdx_x3f_loop___redArg(x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_array_get_size(x_2);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
x_17 = 0;
lean_inc(x_1);
x_18 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_16, x_13, x_12, x_1, x_15, x_17);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_50; 
x_19 = lean_ctor_get(x_18, 0);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
x_20 = x_18;
x_21 = x_50;
goto block_49;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_19, 7);
lean_inc_ref(x_23);
lean_dec(x_19);
lean_inc(x_1);
x_24 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_1, x_22);
lean_dec_ref(x_22);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_del_object(x_20);
x_27 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__3);
x_28 = l_Lean_MessageData_ofName(x_1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_29, x_3, x_4, x_5, x_6);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_1);
x_31 = lean_array_fget(x_23, x_24);
lean_dec(x_24);
lean_dec_ref(x_23);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
switch (x_32) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__5));
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_33);
x_34 = x_20;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__7));
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_37);
x_38 = x_20;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
case 1:
{
if (x_2 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__9));
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_41);
x_42 = x_20;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
else
{
lean_del_object(x_20);
goto block_10;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__11));
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_45);
x_46 = x_20;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
else
{
lean_del_object(x_20);
goto block_10;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_18);
x_51 = l_Lean_MessageData_ofName(x_1);
x_52 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__13, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__13);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_53, x_3, x_4, x_5, x_6);
return x_54;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__1));
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 1;
x_11 = 0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_10, x_11, x_10, x_11, x_12, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_13, 0);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_23 = x_13;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), x_1, x_2, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_20 = x_10;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_18; uint8_t x_19; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_5);
x_19 = l_Lean_Environment_hasUnsafe(x_5, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Environment_hasUnsafe(x_5, x_7);
x_9 = x_20;
goto block_17;
}
else
{
lean_dec_ref(x_5);
x_9 = x_19;
goto block_17;
}
block_17:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_22; uint8_t x_23; 
lean_inc_ref(x_9);
x_22 = l_Lean_Expr_cleanupAnnotations(x_9);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__2));
x_35 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__3));
x_36 = l_Lean_Name_mkStr4(x_1, x_2, x_34, x_35);
x_37 = l_Lean_Expr_isConstOf(x_33, x_36);
lean_dec_ref(x_33);
if (x_37 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_32);
lean_dec_ref(x_29);
lean_dec_ref(x_24);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
goto block_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_9);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_29);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_3);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_24);
x_42 = lean_array_push(x_4, x_38);
x_43 = lean_array_push(x_42, x_39);
x_44 = lean_array_push(x_43, x_40);
x_45 = lean_array_push(x_44, x_41);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_46 = l_Lean_Meta_mkAppOptM(x_36, x_45, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_49 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual(x_5, x_47, x_48, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Level_ofNat(x_6);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_52 = l_Lean_Meta_PProdN_pack(x_51, x_50, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = 1;
x_55 = l_Lean_Meta_mkForallFVars(x_8, x_53, x_48, x_7, x_7, x_54, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_55;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_52;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_56 = lean_ctor_get(x_49, 0);
x_63 = !lean_is_exclusive(x_49);
if (x_63 == 0)
{
x_57 = x_49;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
return x_46;
}
}
}
}
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__1);
x_16 = l_Lean_MessageData_ofExpr(x_9);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___closed__3);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_19, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__3(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = lean_array_uget_borrowed(x_5, x_4);
x_17 = lean_array_get_borrowed(x_13, x_1, x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_17);
x_20 = lean_array_push(x_19, x_17);
x_21 = 1;
lean_inc(x_16);
x_22 = l_Lean_Meta_mkForallFVars(x_20, x_16, x_15, x_2, x_2, x_21, x_6, x_7, x_8, x_9);
lean_dec_ref(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_array_uset(x_5, x_4, x_14);
x_25 = 1;
x_26 = lean_usize_add(x_4, x_25);
x_27 = lean_array_uset(x_24, x_4, x_23);
x_4 = x_26;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec_ref(x_5);
x_29 = lean_ctor_get(x_22, 0);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
x_30 = x_22;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__3(x_1, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get_borrowed(x_12, x_5, x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_13);
x_14 = lean_infer_type(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_16 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual(x_2, x_15, x_3, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_size(x_17);
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__3(x_5, x_3, x_18, x_4, x_17, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_19;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_16;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_21 = x_14;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Expr_app___override(x_1, x_2);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_69);
x_70 = lean_infer_type(x_69, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_72 = l_Lean_Meta_PProdN_reduceProjs(x_71, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_74 = l_Lean_Meta_mkExpectedTypeHint(x_69, x_73, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
x_76 = l_Lean_Meta_PProdN_mk(x_3, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Expr_app___override(x_75, x_77);
if (x_11 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_12, x_13);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_80 = l_Lean_Meta_PProdN_projM(x_14, x_79, x_78, x_16, x_17, x_18, x_19);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_21 = x_81;
x_22 = x_16;
x_23 = x_17;
x_24 = x_18;
x_25 = x_19;
goto block_68;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_80;
}
}
else
{
lean_dec(x_12);
x_21 = x_78;
x_22 = x_16;
x_23 = x_17;
x_24 = x_18;
x_25 = x_19;
goto block_68;
}
}
else
{
lean_dec(x_75);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_76;
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
return x_74;
}
}
else
{
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
return x_72;
}
}
else
{
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
return x_70;
}
block_68:
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
x_27 = l_Lean_Meta_mkLambdaFVars(x_15, x_21, x_4, x_5, x_4, x_5, x_26, x_22, x_23, x_24, x_25);
lean_dec_ref(x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_mkLambdaFVars(x_6, x_28, x_4, x_5, x_4, x_5, x_26, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = 0;
x_32 = l_Lean_Meta_mkLambdaFVars(x_7, x_30, x_5, x_5, x_4, x_5, x_31, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_67; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(x_33, x_23);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8));
x_37 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_36);
lean_inc(x_37);
x_38 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_37, x_24);
x_39 = lean_ctor_get(x_38, 0);
x_67 = !lean_is_exclusive(x_38);
if (x_67 == 0)
{
x_40 = x_38;
x_41 = x_67;
goto block_66;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_42; 
x_42 = lean_unbox(x_39);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_35);
x_43 = x_40;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_35);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_del_object(x_40);
x_46 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1);
lean_inc(x_35);
x_47 = l_Lean_indentExpr(x_35);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_37, x_48, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_49, 0);
lean_dec(x_57);
x_50 = x_49;
x_51 = x_56;
goto block_55;
}
else
{
lean_dec(x_49);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_35);
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_35);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_35);
x_58 = lean_ctor_get(x_49, 0);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
x_59 = x_49;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_32;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_29;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_4);
x_22 = lean_unbox(x_5);
x_23 = lean_unbox(x_11);
x_24 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2(x_1, x_2, x_3, x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__7(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_12 = l_Lean_Meta_PProdN_reduceProjs(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_12, 0);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
x_21 = x_12;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__7(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget_borrowed(x_4, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_inc_ref(x_1);
x_15 = lean_array_push(x_14, x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_12);
x_16 = l_Lean_Meta_instantiateForall(x_12, x_15, x_5, x_6, x_7, x_8);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_19, x_3, x_17);
x_3 = x_21;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_16, 0);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
x_25 = x_16;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_21; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
x_8 = x_5;
x_9 = x_21;
goto block_20;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___lam__0___boxed), 7, 1);
lean_closure_set(x_12, 0, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_12);
x_13 = x_8;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_11, x_2, x_13);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_instInhabitedExpr;
x_9 = l_instInhabitedOfMonad___redArg(x_1, x_8);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___lam__0___boxed), 11, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_5);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_6, x_7, x_8, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
x_19 = x_17;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
x_26 = lean_ctor_get(x_17, 0);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
x_27 = x_17;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_98; 
x_11 = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0);
x_12 = l_ReaderT_instMonad___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
x_98 = !lean_is_exclusive(x_12);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_12, 1);
lean_dec(x_99);
x_14 = x_12;
x_15 = x_98;
goto block_97;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_95; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_95 = !lean_is_exclusive(x_13);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_13, 1);
lean_dec(x_96);
x_20 = x_13;
x_21 = x_95;
goto block_94;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__1));
x_23 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__2));
lean_inc_ref(x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_19);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_18);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_29, 0, x_17);
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_27);
lean_ctor_set(x_20, 3, x_28);
lean_ctor_set(x_20, 2, x_29);
lean_ctor_set(x_20, 1, x_22);
lean_ctor_set(x_20, 0, x_26);
x_30 = x_20;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_26);
lean_ctor_set(x_93, 1, x_22);
lean_ctor_set(x_93, 2, x_29);
lean_ctor_set(x_93, 3, x_28);
lean_ctor_set(x_93, 4, x_27);
x_30 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_31; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_30);
x_31 = x_14;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_30);
lean_ctor_set(x_91, 1, x_23);
x_31 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_88; 
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = lean_ctor_get(x_32, 0);
x_88 = !lean_is_exclusive(x_32);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_32, 1);
lean_dec(x_89);
x_34 = x_32;
x_35 = x_88;
goto block_87;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_85; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 2);
x_38 = lean_ctor_get(x_33, 3);
x_39 = lean_ctor_get(x_33, 4);
x_85 = !lean_is_exclusive(x_33);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_33, 1);
lean_dec(x_86);
x_40 = x_33;
x_41 = x_85;
goto block_84;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__3));
x_43 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__4));
lean_inc_ref(x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_48, 0, x_38);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_49, 0, x_37);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_47);
lean_ctor_set(x_40, 3, x_48);
lean_ctor_set(x_40, 2, x_49);
lean_ctor_set(x_40, 1, x_42);
lean_ctor_set(x_40, 0, x_46);
x_50 = x_40;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_46);
lean_ctor_set(x_83, 1, x_42);
lean_ctor_set(x_83, 2, x_49);
lean_ctor_set(x_83, 3, x_48);
lean_ctor_set(x_83, 4, x_47);
x_50 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_51; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_43);
lean_ctor_set(x_34, 0, x_50);
x_51 = x_34;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_50);
lean_ctor_set(x_81, 1, x_43);
x_51 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_array_get_size(x_5);
x_53 = lean_array_get_size(x_1);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec_ref(x_51);
lean_dec(x_4);
lean_dec_ref(x_1);
x_55 = lean_apply_6(x_2, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_56, 0, x_51);
x_57 = lean_box(0);
x_58 = 0;
x_59 = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_59, 0, x_56);
x_60 = lean_box(x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_get_borrowed(x_62, x_1, x_52);
x_64 = lean_ctor_get(x_63, 1);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_68 = lean_apply_6(x_67, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_unbox(x_66);
x_71 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg(x_5, x_1, x_2, x_3, x_4, x_65, x_70, x_69, x_3, x_6, x_7, x_8, x_9);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_72 = lean_ctor_get(x_68, 0);
x_79 = !lean_is_exclusive(x_68);
if (x_79 == 0)
{
x_73 = x_68;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_1, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg(x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_7);
x_17 = lean_unbox(x_9);
x_18 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg(x_1, x_2, x_3, x_15, x_5, x_6, x_16, x_8, x_17, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___closed__0));
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg(x_2, x_3, x_4, x_1, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
x_8 = x_5;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = 0;
x_13 = lean_box(x_12);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_13);
x_14 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_7);
x_14 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_15);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15(x_10, x_11, x_2);
x_13 = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__10(x_10, x_11, x_2);
x_13 = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Level_ofNat(x_1);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc_ref(x_16);
lean_inc(x_22);
x_23 = l_Lean_Meta_PProdN_mk(x_22, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_size(x_2);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_24);
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__6(x_24, x_25, x_3, x_2, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_array_size(x_27);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
x_29 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__7(x_28, x_3, x_27, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_box(x_5);
x_32 = lean_box(x_6);
x_33 = lean_box(x_11);
lean_inc(x_14);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___boxed), 20, 14);
lean_closure_set(x_34, 0, x_4);
lean_closure_set(x_34, 1, x_24);
lean_closure_set(x_34, 2, x_22);
lean_closure_set(x_34, 3, x_31);
lean_closure_set(x_34, 4, x_32);
lean_closure_set(x_34, 5, x_16);
lean_closure_set(x_34, 6, x_7);
lean_closure_set(x_34, 7, x_8);
lean_closure_set(x_34, 8, x_9);
lean_closure_set(x_34, 9, x_10);
lean_closure_set(x_34, 10, x_33);
lean_closure_set(x_34, 11, x_12);
lean_closure_set(x_34, 12, x_13);
lean_closure_set(x_34, 13, x_14);
x_35 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___closed__0));
x_36 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_14, x_35);
x_37 = l_Array_zip___redArg(x_36, x_30);
lean_dec(x_30);
lean_dec_ref(x_36);
x_38 = 0;
x_39 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_15, x_37, x_34, x_38, x_17, x_18, x_19, x_20);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_40 = lean_ctor_get(x_29, 0);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
x_41 = x_29;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
x_48 = lean_ctor_get(x_26, 0);
x_55 = !lean_is_exclusive(x_26);
if (x_55 == 0)
{
x_49 = x_26;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_26);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
size_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_23 = lean_unbox(x_5);
x_24 = lean_unbox(x_6);
x_25 = lean_unbox(x_11);
x_26 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3(x_1, x_2, x_22, x_4, x_23, x_24, x_7, x_8, x_9, x_10, x_25, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_array_fget_borrowed(x_4, x_6);
x_13 = lean_array_get_size(x_1);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_14 = l_Lean_Meta_PProdN_proj(x_13, x_6, x_2, x_3);
lean_inc(x_12);
x_15 = l_Lean_Expr_app___override(x_12, x_14);
x_16 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_17 = lean_array_push(x_7, x_15);
x_5 = x_11;
x_6 = x_16;
x_7 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_inc_ref(x_7);
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg(x_1, x_2, x_7, x_1, x_13, x_3, x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_16 = l_Lean_Meta_PProdN_pack(x_4, x_15, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_array_push(x_19, x_7);
x_21 = 1;
x_22 = l_Lean_Meta_mkLambdaFVars(x_20, x_17, x_5, x_6, x_5, x_6, x_21, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_20);
return x_22;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
x_14 = lean_unbox(x_6);
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_array_fget_borrowed(x_4, x_6);
x_13 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0);
x_14 = lean_array_get_borrowed(x_13, x_1, x_6);
lean_inc_ref(x_2);
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(x_14, x_2);
lean_inc_ref(x_3);
x_16 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(x_14, x_3);
x_17 = l_Array_append___redArg(x_15, x_16);
lean_dec(x_16);
lean_inc(x_12);
x_18 = l_Lean_mkAppN(x_12, x_17);
lean_dec_ref(x_17);
x_19 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_20 = lean_array_push(x_7, x_18);
x_5 = x_11;
x_6 = x_19;
x_7 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_array_get_size(x_1);
lean_inc_ref(x_3);
x_18 = l_Lean_Meta_PProdN_projs(x_17, x_2, x_3);
lean_inc_ref(x_11);
x_19 = l_Lean_Meta_PProdN_projs(x_17, x_4, x_11);
x_20 = lean_array_get_size(x_5);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg(x_6, x_18, x_19, x_5, x_20, x_7, x_21);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_23 = l_Lean_Meta_PProdN_mk(x_8, x_22, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_3);
x_28 = lean_array_push(x_27, x_11);
x_29 = 1;
x_30 = l_Lean_Meta_mkLambdaFVars(x_28, x_24, x_9, x_10, x_9, x_10, x_29, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_28);
return x_30;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_9);
x_18 = lean_unbox(x_10);
x_19 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_18, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_inc_ref(x_10);
x_18 = lean_array_push(x_17, x_10);
x_19 = l_Lean_Expr_beta(x_1, x_18);
x_20 = lean_box(x_8);
x_21 = lean_box(x_9);
lean_inc_ref(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__5___boxed), 16, 10);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_10);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_20);
lean_closure_set(x_22, 9, x_21);
x_23 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__1));
x_24 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_23, x_19, x_22, x_11, x_12, x_13, x_14);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_8);
x_17 = lean_unbox(x_9);
x_18 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__18));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__2);
x_14 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__5);
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__9);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_62; 
x_27 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_28 = x_19;
x_29 = x_62;
goto block_61;
}
else
{
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_32 = l_Lean_EnvironmentHeader_moduleNames(x_31);
x_33 = lean_array_get(x_30, x_32, x_27);
lean_dec(x_27);
lean_dec_ref(x_32);
x_34 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__11);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__13);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofName(x_33);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__15);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_note(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__7);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__17);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_33);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__19);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_note(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_57);
x_58 = x_28;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_18; 
x_8 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg(x_1, x_2, x_6);
x_9 = lean_ctor_get(x_8, 0);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
x_10 = x_8;
x_11 = x_18;
goto block_17;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_unknownIdentifierMessageTag;
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_32; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 3);
x_12 = lean_ctor_get(x_5, 4);
x_13 = lean_ctor_get(x_5, 5);
x_14 = lean_ctor_get(x_5, 6);
x_15 = lean_ctor_get(x_5, 7);
x_16 = lean_ctor_get(x_5, 8);
x_17 = lean_ctor_get(x_5, 9);
x_18 = lean_ctor_get(x_5, 10);
x_19 = lean_ctor_get(x_5, 11);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*14);
x_21 = lean_ctor_get(x_5, 12);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_23 = lean_ctor_get(x_5, 13);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
x_24 = x_5;
x_25 = x_32;
goto block_31;
}
else
{
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
if (x_25 == 0)
{
lean_ctor_set(x_24, 5, x_26);
x_27 = x_24;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_10);
lean_ctor_set(x_30, 3, x_11);
lean_ctor_set(x_30, 4, x_12);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_14);
lean_ctor_set(x_30, 7, x_15);
lean_ctor_set(x_30, 8, x_16);
lean_ctor_set(x_30, 9, x_17);
lean_ctor_set(x_30, 10, x_18);
lean_ctor_set(x_30, 11, x_19);
lean_ctor_set(x_30, 12, x_21);
lean_ctor_set(x_30, 13, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*14, x_20);
lean_ctor_set_uint8(x_30, sizeof(void*)*14 + 1, x_22);
x_27 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_28; 
x_28 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_2, x_3, x_4, x_27, x_6);
lean_dec_ref(x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg(x_1, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___closed__1);
x_9 = 0;
lean_inc(x_2);
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0___closed__1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg(x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg(x_7, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = 0;
lean_inc(x_1);
x_10 = l_Lean_Environment_findConstVal_x3f(x_8, x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_13 = x_10;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_mkLevelParam(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_19; 
x_8 = lean_ctor_get(x_7, 0);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
x_9 = x_7;
x_10 = x_19;
goto block_18;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__1(x_11, x_12);
x_14 = l_Lean_mkConst(x_1, x_13);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_14);
x_15 = x_9;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_7, 0);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
x_21 = x_7;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_3, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_6, x_14);
if (x_15 == 1)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_40; 
x_17 = l_Lean_instInhabitedDefinitionVal_default;
x_18 = lean_array_get_borrowed(x_17, x_1, x_7);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_6, x_22);
lean_dec(x_6);
lean_inc_ref(x_11);
lean_inc(x_21);
x_40 = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0(x_21, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_box(x_15);
x_43 = lean_box(x_2);
x_44 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_44, 0, x_41);
lean_closure_set(x_44, 1, x_42);
lean_closure_set(x_44, 2, x_43);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_20);
x_45 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg(x_20, x_44, x_15, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0);
x_48 = lean_array_get_borrowed(x_47, x_3, x_7);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_4);
lean_inc(x_48);
x_49 = l_Lean_Elab_FixedParamPerm_instantiateLambda(x_48, x_46, x_4, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_array_fget_borrowed(x_5, x_7);
x_52 = l_Lean_Expr_eta(x_50);
lean_inc(x_51);
x_53 = l_Lean_Expr_app___override(x_51, x_52);
x_24 = x_53;
goto block_28;
}
else
{
x_29 = x_49;
goto block_39;
}
}
else
{
x_29 = x_45;
goto block_39;
}
}
else
{
x_29 = x_40;
goto block_39;
}
block_28:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_nat_add(x_7, x_22);
lean_dec(x_7);
x_26 = lean_array_push(x_8, x_24);
x_6 = x_23;
x_7 = x_25;
x_8 = x_26;
goto _start;
}
block_39:
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_24 = x_30;
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_31 = lean_ctor_get(x_29, 0);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
x_32 = x_29;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31) {
_start:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_box(x_7);
x_34 = lean_box(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_27);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___boxed), 15, 9);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_27);
lean_closure_set(x_35, 4, x_4);
lean_closure_set(x_35, 5, x_5);
lean_closure_set(x_35, 6, x_6);
lean_closure_set(x_35, 7, x_33);
lean_closure_set(x_35, 8, x_34);
x_36 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__1));
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_37 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_36, x_3, x_35, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_167; 
x_38 = lean_ctor_get(x_37, 0);
x_167 = !lean_is_exclusive(x_37);
if (x_167 == 0)
{
x_39 = x_37;
x_40 = x_167;
goto block_166;
}
else
{
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__2));
x_42 = l_Lean_Name_mkStr3(x_9, x_10, x_41);
if (x_40 == 0)
{
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_11);
x_43 = x_39;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_11);
x_43 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_12);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_13);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_14);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_15);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_38);
x_50 = lean_unsigned_to_nat(7u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
x_52 = lean_array_push(x_51, x_43);
x_53 = lean_array_push(x_52, x_44);
x_54 = lean_array_push(x_53, x_45);
x_55 = lean_array_push(x_54, x_46);
x_56 = lean_array_push(x_55, x_47);
x_57 = lean_array_push(x_56, x_48);
x_58 = lean_array_push(x_57, x_49);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_59 = l_Lean_Meta_mkAppOptM(x_42, x_58, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_array_get_size(x_2);
x_62 = lean_mk_empty_array_with_capacity(x_61);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc_ref(x_18);
x_63 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg(x_16, x_8, x_17, x_18, x_2, x_61, x_5, x_62, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_inc(x_31);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_65 = l_Lean_Meta_PProdN_pack(x_6, x_64, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_155; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8));
x_68 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_67);
lean_inc(x_68);
x_128 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_68, x_30);
x_129 = lean_ctor_get(x_128, 0);
x_155 = !lean_is_exclusive(x_128);
if (x_155 == 0)
{
x_130 = x_128;
x_131 = x_155;
goto block_154;
}
else
{
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = x_155;
goto block_154;
}
block_116:
{
uint8_t x_74; lean_object* x_75; 
x_74 = 1;
x_75 = l_Lean_Meta_mkLambdaFVars(x_27, x_69, x_7, x_8, x_7, x_8, x_74, x_70, x_71, x_72, x_73);
lean_dec_ref(x_27);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_Meta_mkLambdaFVars(x_22, x_76, x_7, x_8, x_7, x_8, x_74, x_70, x_71, x_72, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_Meta_mkLambdaFVars(x_2, x_78, x_7, x_8, x_7, x_8, x_74, x_70, x_71, x_72, x_73);
lean_dec_ref(x_2);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = 0;
x_82 = l_Lean_Meta_mkLambdaFVars(x_18, x_80, x_8, x_8, x_7, x_8, x_81, x_70, x_71, x_72, x_73);
lean_dec_ref(x_18);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_115; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(x_83, x_71);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
lean_inc(x_68);
x_86 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_68, x_72);
x_87 = lean_ctor_get(x_86, 0);
x_115 = !lean_is_exclusive(x_86);
if (x_115 == 0)
{
x_88 = x_86;
x_89 = x_115;
goto block_114;
}
else
{
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_box(0);
x_89 = x_115;
goto block_114;
}
block_114:
{
uint8_t x_90; 
x_90 = lean_unbox(x_87);
lean_dec(x_87);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
if (x_89 == 0)
{
lean_ctor_set(x_88, 0, x_85);
x_91 = x_88;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_85);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_del_object(x_88);
x_94 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__2___closed__1);
lean_inc(x_85);
x_95 = l_Lean_indentExpr(x_85);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_68, x_96, x_70, x_71, x_72, x_73);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; uint8_t x_104; 
x_104 = !lean_is_exclusive(x_97);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_97, 0);
lean_dec(x_105);
x_98 = x_97;
x_99 = x_104;
goto block_103;
}
else
{
lean_dec(x_97);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
lean_ctor_set(x_98, 0, x_85);
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_85);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_85);
x_106 = lean_ctor_get(x_97, 0);
x_113 = !lean_is_exclusive(x_97);
if (x_113 == 0)
{
x_107 = x_97;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_97);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
return x_82;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec_ref(x_18);
return x_79;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
return x_77;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
return x_75;
}
}
block_127:
{
lean_object* x_121; 
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_118);
lean_inc_ref(x_117);
x_121 = l_Lean_Meta_mkExpectedTypeHint(x_60, x_66, x_117, x_118, x_119, x_120);
if (lean_obj_tag(x_121) == 0)
{
if (x_23 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_24, x_25);
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_118);
lean_inc_ref(x_117);
x_124 = l_Lean_Meta_PProdN_projM(x_26, x_123, x_122, x_117, x_118, x_119, x_120);
lean_dec(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_69 = x_125;
x_70 = x_117;
x_71 = x_118;
x_72 = x_119;
x_73 = x_120;
goto block_116;
}
else
{
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_68);
lean_dec_ref(x_27);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
return x_124;
}
}
else
{
lean_object* x_126; 
lean_dec(x_24);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
lean_dec_ref(x_121);
x_69 = x_126;
x_70 = x_117;
x_71 = x_118;
x_72 = x_119;
x_73 = x_120;
goto block_116;
}
}
else
{
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_68);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
return x_121;
}
}
block_154:
{
uint8_t x_132; 
x_132 = lean_unbox(x_129);
lean_dec(x_129);
if (x_132 == 0)
{
lean_del_object(x_130);
x_117 = x_28;
x_118 = x_29;
x_119 = x_30;
x_120 = x_31;
goto block_127;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__4);
lean_inc(x_66);
x_134 = l_Lean_MessageData_ofExpr(x_66);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__6, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___closed__6);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_24);
x_138 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_24, x_25);
x_139 = l_Nat_reprFast(x_138);
if (x_131 == 0)
{
lean_ctor_set_tag(x_130, 3);
lean_ctor_set(x_130, 0, x_139);
x_140 = x_130;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_153, 0, x_139);
x_140 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = l_Lean_MessageData_ofFormat(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_inc(x_68);
x_143 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_68, x_142, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_143) == 0)
{
lean_dec_ref(x_143);
x_117 = x_28;
x_118 = x_29;
x_119 = x_30;
x_120 = x_31;
goto block_127;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_151; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
x_144 = lean_ctor_get(x_143, 0);
x_151 = !lean_is_exclusive(x_143);
if (x_151 == 0)
{
x_145 = x_143;
x_146 = x_151;
goto block_150;
}
else
{
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_box(0);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_146 == 0)
{
x_147 = x_145;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_144);
x_147 = x_149;
goto block_148;
}
block_148:
{
return x_147;
}
}
}
}
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_2);
return x_65;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_dec(x_60);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_6);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_63, 0);
x_163 = !lean_is_exclusive(x_63);
if (x_163 == 0)
{
x_157 = x_63;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_63);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_59;
}
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_unbox(x_7);
x_34 = lean_unbox(x_8);
x_35 = lean_unbox(x_23);
x_36 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_33, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_35, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_14);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj(x_1, x_4, x_14, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_20 = lean_array_push(x_5, x_16);
x_3 = x_18;
x_4 = x_19;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_15, 0);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
x_23 = x_15;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_7);
x_17 = lean_box(0);
x_18 = l_Lean_Name_str___override(x_17, x_16);
x_10 = x_18;
goto block_15;
}
else
{
lean_object* x_19; 
lean_dec(x_7);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__1));
x_10 = x_19;
goto block_15;
}
block_15:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_array_fget_borrowed(x_2, x_4);
x_12 = lean_array_get_borrowed(x_8, x_1, x_4);
lean_inc(x_11);
lean_inc(x_12);
x_13 = l_Lean_Expr_app___override(x_12, x_11);
x_14 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_15 = lean_array_push(x_5, x_13);
x_3 = x_10;
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_10 = l_Lean_Expr_containsFVar(x_1, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_box(x_10);
x_14 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__14(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_PProdN_mk(x_1, x_2, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_array_push(x_20, x_18);
x_22 = l_Lean_Expr_beta(x_3, x_21);
x_23 = lean_array_get_size(x_4);
x_24 = l_Lean_Meta_PProdN_proj(x_23, x_5, x_6, x_22);
x_25 = lean_array_get_borrowed(x_7, x_4, x_5);
lean_inc(x_25);
x_26 = l_Lean_Expr_app___override(x_25, x_24);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_27 = l_Lean_Meta_PProdN_reduceProjs(x_26, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_array_size(x_2);
lean_inc_ref(x_2);
x_30 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__14(x_28, x_29, x_8, x_2);
x_31 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(x_30, x_2);
x_32 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___redArg(x_30, x_11);
x_33 = l_Array_append___redArg(x_31, x_32);
lean_dec(x_32);
x_34 = 1;
x_35 = l_Lean_Meta_mkForallFVars(x_33, x_28, x_9, x_10, x_10, x_34, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_44; 
x_36 = lean_ctor_get(x_35, 0);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
x_37 = x_35;
x_38 = x_44;
goto block_43;
}
else
{
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_30);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_39);
x_40 = x_37;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_30);
x_45 = lean_ctor_get(x_35, 0);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
x_46 = x_35;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_53 = lean_ctor_get(x_27, 0);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
x_54 = x_27;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_27);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_61 = lean_ctor_get(x_17, 0);
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
x_62 = x_17;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_17);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = lean_unbox(x_9);
x_19 = lean_unbox(x_10);
x_20 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_19, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__16(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__6___closed__1));
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__16(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_18 = lean_box_usize(x_7);
x_19 = lean_box(x_8);
x_20 = lean_box(x_9);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_21 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__0___boxed), 16, 10);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_12);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_18);
lean_closure_set(x_21, 8, x_19);
lean_closure_set(x_21, 9, x_20);
x_22 = lean_array_get_size(x_12);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg(x_3, x_12, x_22, x_10, x_23);
lean_dec_ref(x_12);
lean_dec_ref(x_3);
x_25 = lean_array_size(x_24);
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__16(x_25, x_7, x_24);
x_27 = 0;
x_28 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_11, x_26, x_21, x_27, x_13, x_14, x_15, x_16);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
x_20 = lean_unbox(x_9);
x_21 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg___closed__0);
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_7, x_15);
if (x_16 == 1)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0);
x_20 = lean_array_size(x_1);
x_21 = 0;
lean_inc_ref(x_1);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13(x_20, x_21, x_1);
x_23 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__1);
x_24 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed__const__1));
x_25 = lean_box(x_16);
x_26 = lean_box(x_5);
lean_inc_ref(x_4);
lean_inc(x_8);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_27 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___lam__1___boxed), 17, 11);
lean_closure_set(x_27, 0, x_19);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_8);
lean_closure_set(x_27, 4, x_4);
lean_closure_set(x_27, 5, x_18);
lean_closure_set(x_27, 6, x_24);
lean_closure_set(x_27, 7, x_25);
lean_closure_set(x_27, 8, x_26);
lean_closure_set(x_27, 9, x_15);
lean_closure_set(x_27, 10, x_23);
x_28 = l_Array_zip___redArg(x_22, x_6);
lean_dec_ref(x_22);
x_29 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_30 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_23, x_28, x_27, x_29, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_7, x_32);
lean_dec(x_7);
x_34 = lean_nat_add(x_8, x_32);
lean_dec(x_8);
x_35 = lean_array_push(x_9, x_31);
x_7 = x_33;
x_8 = x_34;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_30, 0);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
x_38 = x_30;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
x_16 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30) {
_start:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_get_size(x_26);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_2);
lean_inc_ref(x_1);
x_34 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg(x_1, x_26, x_32, x_2, x_33, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc_ref(x_1);
lean_inc_ref(x_3);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___boxed), 9, 2);
lean_closure_set(x_36, 0, x_3);
lean_closure_set(x_36, 1, x_1);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc_ref(x_4);
x_37 = l_Lean_Meta_PProdN_genMk___redArg(x_4, x_36, x_35, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_2);
lean_inc(x_5);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_40 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg(x_6, x_7, x_8, x_9, x_10, x_11, x_5, x_2, x_39, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Array_unzip___redArg(x_41);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_box(x_14);
x_46 = lean_box(x_10);
x_47 = lean_box(x_23);
lean_inc(x_5);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__7___boxed), 32, 26);
lean_closure_set(x_48, 0, x_12);
lean_closure_set(x_48, 1, x_8);
lean_closure_set(x_48, 2, x_9);
lean_closure_set(x_48, 3, x_44);
lean_closure_set(x_48, 4, x_2);
lean_closure_set(x_48, 5, x_13);
lean_closure_set(x_48, 6, x_45);
lean_closure_set(x_48, 7, x_46);
lean_closure_set(x_48, 8, x_15);
lean_closure_set(x_48, 9, x_16);
lean_closure_set(x_48, 10, x_3);
lean_closure_set(x_48, 11, x_1);
lean_closure_set(x_48, 12, x_7);
lean_closure_set(x_48, 13, x_17);
lean_closure_set(x_48, 14, x_38);
lean_closure_set(x_48, 15, x_6);
lean_closure_set(x_48, 16, x_18);
lean_closure_set(x_48, 17, x_19);
lean_closure_set(x_48, 18, x_20);
lean_closure_set(x_48, 19, x_21);
lean_closure_set(x_48, 20, x_22);
lean_closure_set(x_48, 21, x_26);
lean_closure_set(x_48, 22, x_47);
lean_closure_set(x_48, 23, x_24);
lean_closure_set(x_48, 24, x_25);
lean_closure_set(x_48, 25, x_5);
x_49 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___closed__0));
x_50 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_5, x_49);
x_51 = l_Array_zip___redArg(x_50, x_43);
lean_dec(x_43);
lean_dec_ref(x_50);
x_52 = 0;
x_53 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_4, x_51, x_48, x_52, x_27, x_28, x_29, x_30);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_38);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_40, 0);
x_61 = !lean_is_exclusive(x_40);
if (x_61 == 0)
{
x_55 = x_40;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_37;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_34, 0);
x_69 = !lean_is_exclusive(x_34);
if (x_69 == 0)
{
x_63 = x_34;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_34);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
_start:
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_unbox(x_10);
x_33 = lean_unbox(x_14);
x_34 = lean_unbox(x_23);
x_35 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32, x_11, x_12, x_13, x_33, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_34, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec_ref(x_11);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_4, x_12);
if (x_13 == 1)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_fget_borrowed(x_3, x_5);
x_17 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___closed__1));
x_18 = lean_array_get_borrowed(x_15, x_1, x_5);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_array_get_borrowed(x_15, x_2, x_5);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_16);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_array_push(x_24, x_19);
x_26 = lean_array_push(x_25, x_21);
x_27 = lean_array_push(x_26, x_22);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_28 = l_Lean_Meta_mkAppOptM(x_17, x_27, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_4, x_30);
lean_dec(x_4);
x_32 = lean_nat_add(x_5, x_30);
lean_dec(x_5);
x_33 = lean_array_push(x_6, x_29);
x_4 = x_31;
x_5 = x_32;
x_6 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_28, 0);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
x_36 = x_28;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, uint8_t x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29) {
_start:
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__1));
lean_inc(x_29);
lean_inc_ref(x_28);
x_32 = l_Lean_Core_mkFreshUserName(x_31, x_28, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_box(x_4);
x_35 = lean_box(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_25);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__4___boxed), 12, 6);
lean_closure_set(x_36, 0, x_25);
lean_closure_set(x_36, 1, x_1);
lean_closure_set(x_36, 2, x_2);
lean_closure_set(x_36, 3, x_3);
lean_closure_set(x_36, 4, x_34);
lean_closure_set(x_36, 5, x_35);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_1);
x_37 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_33, x_1, x_36, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_array_get_size(x_25);
x_40 = lean_mk_empty_array_with_capacity(x_39);
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_2);
x_41 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg(x_6, x_7, x_25, x_39, x_2, x_40, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_box(x_5);
x_44 = lean_box(x_4);
x_45 = lean_box(x_22);
lean_inc_ref(x_10);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__8___boxed), 31, 25);
lean_closure_set(x_46, 0, x_8);
lean_closure_set(x_46, 1, x_2);
lean_closure_set(x_46, 2, x_9);
lean_closure_set(x_46, 3, x_10);
lean_closure_set(x_46, 4, x_11);
lean_closure_set(x_46, 5, x_12);
lean_closure_set(x_46, 6, x_13);
lean_closure_set(x_46, 7, x_25);
lean_closure_set(x_46, 8, x_1);
lean_closure_set(x_46, 9, x_43);
lean_closure_set(x_46, 10, x_6);
lean_closure_set(x_46, 11, x_38);
lean_closure_set(x_46, 12, x_3);
lean_closure_set(x_46, 13, x_44);
lean_closure_set(x_46, 14, x_14);
lean_closure_set(x_46, 15, x_15);
lean_closure_set(x_46, 16, x_16);
lean_closure_set(x_46, 17, x_17);
lean_closure_set(x_46, 18, x_18);
lean_closure_set(x_46, 19, x_19);
lean_closure_set(x_46, 20, x_20);
lean_closure_set(x_46, 21, x_21);
lean_closure_set(x_46, 22, x_45);
lean_closure_set(x_46, 23, x_23);
lean_closure_set(x_46, 24, x_24);
x_47 = lean_array_get_size(x_42);
x_48 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___closed__2));
x_49 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_47, x_48);
x_50 = l_Array_zip___redArg(x_49, x_42);
lean_dec(x_42);
lean_dec_ref(x_49);
x_51 = 0;
x_52 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_10, x_50, x_46, x_51, x_26, x_27, x_28, x_29);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_41, 0);
x_60 = !lean_is_exclusive(x_41);
if (x_60 == 0)
{
x_54 = x_41;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_37;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_61 = lean_ctor_get(x_32, 0);
x_68 = !lean_is_exclusive(x_32);
if (x_68 == 0)
{
x_62 = x_32;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_32);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
_start:
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_unbox(x_4);
x_32 = lean_unbox(x_5);
x_33 = lean_unbox(x_22);
x_34 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9(x_1, x_2, x_3, x_31, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_33, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
lean_dec_ref(x_7);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_4, x_12);
if (x_13 == 1)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_fget_borrowed(x_3, x_5);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_16, 2);
x_18 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0);
x_19 = lean_array_get_borrowed(x_18, x_1, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
lean_inc_ref(x_17);
lean_inc(x_19);
x_20 = l_Lean_Elab_FixedParamPerm_instantiateForall(x_19, x_17, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_4, x_22);
lean_dec(x_4);
x_24 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_25 = lean_array_push(x_6, x_21);
x_4 = x_23;
x_5 = x_24;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_27 = lean_ctor_get(x_20, 0);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
x_28 = x_20;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 1)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_38; 
x_16 = lean_array_fget_borrowed(x_4, x_6);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
lean_inc_ref(x_10);
lean_inc(x_19);
x_38 = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0(x_19, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_box(x_14);
x_41 = lean_box(x_1);
x_42 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_42, 0, x_39);
lean_closure_set(x_42, 1, x_40);
lean_closure_set(x_42, 2, x_41);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_18);
x_43 = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__1___redArg(x_18, x_42, x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0);
x_46 = lean_array_get_borrowed(x_45, x_2, x_6);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
lean_inc(x_46);
x_47 = l_Lean_Elab_FixedParamPerm_instantiateLambda(x_46, x_44, x_3, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Expr_eta(x_48);
x_22 = x_49;
goto block_26;
}
else
{
x_27 = x_47;
goto block_37;
}
}
else
{
x_27 = x_43;
goto block_37;
}
}
else
{
x_27 = x_38;
goto block_37;
}
block_26:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_24 = lean_array_push(x_7, x_22);
x_5 = x_21;
x_6 = x_23;
x_7 = x_24;
goto _start;
}
block_37:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_22 = x_28;
goto block_26;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
x_29 = lean_ctor_get(x_27, 0);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
x_30 = x_27;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__9(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = 1;
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Elab_isLatticeTheoretic(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
if (x_4 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
}
else
{
return x_5;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__9(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___closed__0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uget_borrowed(x_3, x_2);
x_11 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___closed__0);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_10);
x_12 = l_Lean_mkArrow(x_10, x_11, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_array_uset(x_3, x_2, x_9);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_14, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_12, 0);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
x_20 = x_12;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg(x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__17));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
x_22 = l_Lean_Elab_FixedParamPerm_instantiateLambda(x_2, x_21, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_243; 
x_23 = lean_ctor_get(x_22, 0);
x_243 = !lean_is_exclusive(x_22);
if (x_243 == 0)
{
x_24 = x_22;
x_25 = x_243;
goto block_242;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_243;
goto block_242;
}
block_242:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_165; uint8_t x_166; 
lean_inc(x_23);
x_37 = l_Lean_Expr_eta(x_23);
x_38 = l_Lean_Meta_PProdN_stripProjs(x_37);
lean_dec_ref(x_37);
x_165 = lean_array_get_size(x_14);
x_166 = lean_nat_dec_lt(x_5, x_165);
if (x_166 == 0)
{
goto block_164;
}
else
{
if (x_166 == 0)
{
goto block_164;
}
else
{
size_t x_167; uint8_t x_168; 
x_167 = lean_usize_of_nat(x_165);
x_168 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__9(x_14, x_7, x_167);
if (x_168 == 0)
{
goto block_164;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_del_object(x_24);
lean_dec_ref(x_6);
x_169 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0));
x_170 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1));
x_171 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15));
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_38);
x_172 = l_Lean_Meta_whnfUntil(x_38, x_171, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_23);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = l_Lean_Expr_cleanupAnnotations(x_174);
x_176 = l_Lean_Expr_isApp(x_175);
if (x_176 == 0)
{
lean_dec_ref(x_175);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_39 = x_16;
x_40 = x_17;
x_41 = x_18;
x_42 = x_19;
goto block_49;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_175, 1);
lean_inc_ref(x_177);
x_178 = l_Lean_Expr_appFnCleanup___redArg(x_175);
x_179 = l_Lean_Expr_isApp(x_178);
if (x_179 == 0)
{
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_39 = x_16;
x_40 = x_17;
x_41 = x_18;
x_42 = x_19;
goto block_49;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_178, 1);
lean_inc_ref(x_180);
x_181 = l_Lean_Expr_appFnCleanup___redArg(x_178);
x_182 = l_Lean_Expr_isApp(x_181);
if (x_182 == 0)
{
lean_dec_ref(x_181);
lean_dec_ref(x_180);
lean_dec_ref(x_177);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_39 = x_16;
x_40 = x_17;
x_41 = x_18;
x_42 = x_19;
goto block_49;
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc_ref(x_183);
x_184 = l_Lean_Expr_appFnCleanup___redArg(x_181);
x_185 = l_Lean_Expr_isApp(x_184);
if (x_185 == 0)
{
lean_dec_ref(x_184);
lean_dec_ref(x_183);
lean_dec_ref(x_180);
lean_dec_ref(x_177);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_39 = x_16;
x_40 = x_17;
x_41 = x_18;
x_42 = x_19;
goto block_49;
}
else
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc_ref(x_186);
x_187 = l_Lean_Expr_appFnCleanup___redArg(x_184);
x_188 = l_Lean_Expr_isConstOf(x_187, x_171);
lean_dec_ref(x_187);
if (x_188 == 0)
{
lean_dec_ref(x_186);
lean_dec_ref(x_183);
lean_dec_ref(x_180);
lean_dec_ref(x_177);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_39 = x_16;
x_40 = x_17;
x_41 = x_18;
x_42 = x_19;
goto block_49;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_38);
x_189 = lean_array_get_size(x_3);
x_190 = lean_mk_empty_array_with_capacity(x_189);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_5);
lean_inc_ref(x_15);
x_191 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg(x_4, x_15, x_3, x_189, x_5, x_190, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = l_Lean_Level_ofNat(x_5);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_192);
lean_inc(x_193);
x_194 = l_Lean_Meta_PProdN_pack(x_193, x_192, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; size_t x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = lean_array_size(x_192);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_192);
x_197 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg(x_196, x_7, x_192, x_18, x_19);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = 0;
lean_inc_ref(x_183);
x_200 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs(x_189, x_183);
x_201 = lean_array_get_size(x_198);
x_202 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__16));
x_203 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_201, x_202);
x_204 = l_Lean_instInhabitedExpr;
x_205 = lean_box(x_199);
x_206 = lean_box(x_168);
x_207 = lean_box(x_11);
x_208 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__9___boxed), 30, 24);
lean_closure_set(x_208, 0, x_195);
lean_closure_set(x_208, 1, x_5);
lean_closure_set(x_208, 2, x_193);
lean_closure_set(x_208, 3, x_205);
lean_closure_set(x_208, 4, x_206);
lean_closure_set(x_208, 5, x_192);
lean_closure_set(x_208, 6, x_200);
lean_closure_set(x_208, 7, x_183);
lean_closure_set(x_208, 8, x_186);
lean_closure_set(x_208, 9, x_204);
lean_closure_set(x_208, 10, x_189);
lean_closure_set(x_208, 11, x_3);
lean_closure_set(x_208, 12, x_180);
lean_closure_set(x_208, 13, x_169);
lean_closure_set(x_208, 14, x_170);
lean_closure_set(x_208, 15, x_177);
lean_closure_set(x_208, 16, x_4);
lean_closure_set(x_208, 17, x_15);
lean_closure_set(x_208, 18, x_8);
lean_closure_set(x_208, 19, x_9);
lean_closure_set(x_208, 20, x_10);
lean_closure_set(x_208, 21, x_207);
lean_closure_set(x_208, 22, x_12);
lean_closure_set(x_208, 23, x_13);
x_209 = l_Array_zip___redArg(x_203, x_198);
lean_dec(x_198);
lean_dec_ref(x_203);
x_210 = 0;
x_211 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_204, x_209, x_208, x_210, x_16, x_17, x_18, x_19);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_219; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_186);
lean_dec_ref(x_183);
lean_dec_ref(x_180);
lean_dec_ref(x_177);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_212 = lean_ctor_get(x_197, 0);
x_219 = !lean_is_exclusive(x_197);
if (x_219 == 0)
{
x_213 = x_197;
x_214 = x_219;
goto block_218;
}
else
{
lean_inc(x_212);
lean_dec(x_197);
x_213 = lean_box(0);
x_214 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_215; 
if (x_214 == 0)
{
x_215 = x_213;
goto block_216;
}
else
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_212);
x_215 = x_217;
goto block_216;
}
block_216:
{
return x_215;
}
}
}
}
else
{
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_186);
lean_dec_ref(x_183);
lean_dec_ref(x_180);
lean_dec_ref(x_177);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_194;
}
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_227; 
lean_dec_ref(x_186);
lean_dec_ref(x_183);
lean_dec_ref(x_180);
lean_dec_ref(x_177);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_220 = lean_ctor_get(x_191, 0);
x_227 = !lean_is_exclusive(x_191);
if (x_227 == 0)
{
x_221 = x_191;
x_222 = x_227;
goto block_226;
}
else
{
lean_inc(x_220);
lean_dec(x_191);
x_221 = lean_box(0);
x_222 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_223; 
if (x_222 == 0)
{
x_223 = x_221;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_220);
x_223 = x_225;
goto block_224;
}
block_224:
{
return x_223;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_173);
lean_dec_ref(x_38);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_228 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1);
x_229 = l_Lean_MessageData_ofExpr(x_23);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__18, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__18);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_232, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; uint8_t x_241; 
lean_dec_ref(x_38);
lean_dec(x_23);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_234 = lean_ctor_get(x_172, 0);
x_241 = !lean_is_exclusive(x_172);
if (x_241 == 0)
{
x_235 = x_172;
x_236 = x_241;
goto block_240;
}
else
{
lean_inc(x_234);
lean_dec(x_172);
x_235 = lean_box(0);
x_236 = x_241;
goto block_240;
}
block_240:
{
lean_object* x_237; 
if (x_236 == 0)
{
x_237 = x_235;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_234);
x_237 = x_239;
goto block_238;
}
block_238:
{
return x_237;
}
}
}
}
}
}
block_36:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1);
x_31 = l_Lean_MessageData_ofExpr(x_23);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__3);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_34, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
return x_35;
}
block_49:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1);
x_44 = l_Lean_MessageData_ofExpr(x_38);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__5);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_47, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
return x_48;
}
block_164:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__0));
x_51 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1));
x_52 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__7));
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_53 = l_Lean_Meta_whnfUntil(x_38, x_52, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_149; 
x_55 = lean_ctor_get(x_54, 0);
x_149 = !lean_is_exclusive(x_54);
if (x_149 == 0)
{
x_56 = x_54;
x_57 = x_149;
goto block_148;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Expr_cleanupAnnotations(x_55);
x_59 = l_Lean_Expr_isApp(x_58);
if (x_59 == 0)
{
lean_dec_ref(x_58);
lean_del_object(x_56);
lean_del_object(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_19;
goto block_36;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_58);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_del_object(x_56);
lean_del_object(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_19;
goto block_36;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_del_object(x_56);
lean_del_object(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_19;
goto block_36;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_66);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_68 = l_Lean_Expr_isApp(x_67);
if (x_68 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_del_object(x_56);
lean_del_object(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_19;
goto block_36;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_69);
x_70 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_71 = l_Lean_Expr_isConstOf(x_70, x_52);
lean_dec_ref(x_70);
if (x_71 == 0)
{
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec_ref(x_60);
lean_del_object(x_56);
lean_del_object(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_19;
goto block_36;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_23);
x_72 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__9));
lean_inc_ref(x_69);
if (x_57 == 0)
{
lean_ctor_set(x_56, 0, x_69);
x_73 = x_56;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_69);
x_73 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_74; 
if (x_25 == 0)
{
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_66);
x_74 = x_24;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_66);
x_74 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_63);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_60);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_mk_empty_array_with_capacity(x_77);
lean_inc_ref(x_78);
x_79 = lean_array_push(x_78, x_73);
x_80 = lean_array_push(x_79, x_74);
x_81 = lean_array_push(x_80, x_75);
x_82 = lean_array_push(x_81, x_76);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_83 = l_Lean_Meta_mkAppOptM(x_72, x_82, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_array_get_size(x_3);
x_86 = lean_mk_empty_array_with_capacity(x_85);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_5);
lean_inc_ref(x_15);
x_87 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg(x_71, x_4, x_15, x_3, x_85, x_5, x_86, x_16, x_17, x_18, x_19);
lean_dec_ref(x_3);
lean_dec_ref(x_4);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__10, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__10);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_91 = l_Lean_Meta_PProdN_mk(x_90, x_88, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_84);
x_93 = lean_infer_type(x_84, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_box(x_71);
lean_inc(x_5);
lean_inc_ref(x_6);
x_96 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__0___boxed), 14, 7);
lean_closure_set(x_96, 0, x_50);
lean_closure_set(x_96, 1, x_51);
lean_closure_set(x_96, 2, x_92);
lean_closure_set(x_96, 3, x_78);
lean_closure_set(x_96, 4, x_6);
lean_closure_set(x_96, 5, x_5);
lean_closure_set(x_96, 6, x_95);
x_97 = 0;
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_98 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(x_94, x_96, x_97, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_99);
x_100 = l_Lean_Meta_mkExpectedTypeHint(x_84, x_99, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = lean_box(x_71);
x_103 = lean_box_usize(x_7);
x_104 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__1___boxed), 11, 4);
lean_closure_set(x_104, 0, x_89);
lean_closure_set(x_104, 1, x_6);
lean_closure_set(x_104, 2, x_102);
lean_closure_set(x_104, 3, x_103);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_105 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(x_99, x_104, x_97, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l_Lean_Meta_PProdN_unpack___redArg(x_69, x_85);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__11));
x_110 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_85, x_109);
x_111 = l_Array_zip___redArg(x_110, x_108);
lean_dec(x_108);
lean_dec_ref(x_110);
x_112 = l_Lean_instInhabitedExpr;
x_113 = lean_box_usize(x_7);
x_114 = lean_box(x_97);
x_115 = lean_box(x_71);
x_116 = lean_box(x_11);
x_117 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__3___boxed), 21, 15);
lean_closure_set(x_117, 0, x_5);
lean_closure_set(x_117, 1, x_106);
lean_closure_set(x_117, 2, x_113);
lean_closure_set(x_117, 3, x_101);
lean_closure_set(x_117, 4, x_114);
lean_closure_set(x_117, 5, x_115);
lean_closure_set(x_117, 6, x_15);
lean_closure_set(x_117, 7, x_8);
lean_closure_set(x_117, 8, x_9);
lean_closure_set(x_117, 9, x_10);
lean_closure_set(x_117, 10, x_116);
lean_closure_set(x_117, 11, x_12);
lean_closure_set(x_117, 12, x_13);
lean_closure_set(x_117, 13, x_85);
lean_closure_set(x_117, 14, x_112);
x_118 = 0;
x_119 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_112, x_111, x_117, x_118, x_16, x_17, x_18, x_19);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
x_120 = lean_ctor_get(x_107, 0);
x_127 = !lean_is_exclusive(x_107);
if (x_127 == 0)
{
x_121 = x_107;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_107);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_101);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
x_128 = lean_ctor_get(x_105, 0);
x_135 = !lean_is_exclusive(x_105);
if (x_135 == 0)
{
x_129 = x_105;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_105);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
else
{
lean_dec(x_99);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_100;
}
}
else
{
lean_dec(x_84);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_98;
}
}
else
{
lean_dec(x_92);
lean_dec(x_84);
lean_dec_ref(x_78);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_93;
}
}
else
{
lean_dec(x_84);
lean_dec_ref(x_78);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_91;
}
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_143; 
lean_dec(x_84);
lean_dec_ref(x_78);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
x_136 = lean_ctor_get(x_87, 0);
x_143 = !lean_is_exclusive(x_87);
if (x_143 == 0)
{
x_137 = x_87;
x_138 = x_143;
goto block_142;
}
else
{
lean_inc(x_136);
lean_dec(x_87);
x_137 = lean_box(0);
x_138 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_139; 
if (x_138 == 0)
{
x_139 = x_137;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_136);
x_139 = x_141;
goto block_140;
}
block_140:
{
return x_139;
}
}
}
}
else
{
lean_dec_ref(x_78);
lean_dec_ref(x_69);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_83;
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
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_54);
lean_del_object(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_150 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__1);
x_151 = l_Lean_MessageData_ofExpr(x_23);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__13, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__13);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_154, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_del_object(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_156 = lean_ctor_get(x_53, 0);
x_163 = !lean_is_exclusive(x_53);
if (x_163 == 0)
{
x_157 = x_53;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_53);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox(x_11);
x_23 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9, x_10, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_14);
return x_23;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24_spec__29(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24_spec__29(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24_spec__29(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_16; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
x_7 = x_2;
x_8 = x_16;
goto block_15;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_16;
goto block_15;
}
block_15:
{
uint8_t x_9; 
x_9 = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__24(x_1, x_5);
if (x_9 == 0)
{
lean_del_object(x_7);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_3);
x_11 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_3);
x_11 = x_14;
goto block_13;
}
block_13:
{
x_2 = x_6;
x_3 = x_11;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__2));
x_2 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_st_ref_get(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = 0;
lean_inc(x_2);
x_21 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_1, x_17, x_16, x_2, x_19, x_20);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_22, 6);
x_25 = lean_ctor_get(x_22, 7);
lean_inc_ref(x_25);
x_26 = lean_array_size(x_23);
x_27 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1(x_26, x_27, x_23, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_109; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_30);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get(x_3, x_29, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_33, 1);
x_35 = lean_ctor_get(x_33, 2);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_33, 0);
lean_dec(x_110);
x_36 = x_33;
x_37 = x_109;
goto block_108;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_array_get(x_4, x_30, x_31);
x_39 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed__const__1));
x_40 = lean_box(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_38);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___boxed), 20, 14);
lean_closure_set(x_41, 0, x_32);
lean_closure_set(x_41, 1, x_38);
lean_closure_set(x_41, 2, x_29);
lean_closure_set(x_41, 3, x_30);
lean_closure_set(x_41, 4, x_31);
lean_closure_set(x_41, 5, x_22);
lean_closure_set(x_41, 6, x_39);
lean_closure_set(x_41, 7, x_5);
lean_closure_set(x_41, 8, x_6);
lean_closure_set(x_41, 9, x_7);
lean_closure_set(x_41, 10, x_40);
lean_closure_set(x_41, 11, x_2);
lean_closure_set(x_41, 12, x_23);
lean_closure_set(x_41, 13, x_25);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_42 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg(x_38, x_35, x_41, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_43);
x_44 = lean_infer_type(x_43, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_83 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__8));
x_84 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_83);
lean_inc(x_84);
x_85 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_84, x_12);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_dec(x_84);
x_46 = x_10;
x_47 = x_11;
x_48 = x_12;
x_49 = x_13;
goto block_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__5, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__5);
lean_inc(x_45);
x_89 = l_Lean_MessageData_ofExpr(x_45);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_84, x_90, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
x_46 = x_10;
x_47 = x_11;
x_48 = x_12;
x_49 = x_13;
goto block_82;
}
else
{
lean_dec(x_45);
lean_dec(x_43);
lean_del_object(x_36);
lean_dec(x_34);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_91;
}
}
block_82:
{
lean_object* x_50; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_inc(x_49);
lean_inc_ref(x_48);
x_50 = l_Lean_Meta_elimOptParam(x_45, x_48, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_71; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3);
lean_inc(x_51);
x_53 = l_Lean_collectLevelParams(x_52, x_51);
x_54 = lean_ctor_get(x_53, 2);
x_71 = !lean_is_exclusive(x_53);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_53, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_53, 0);
lean_dec(x_73);
x_55 = x_53;
x_56 = x_71;
goto block_70;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_box(0);
x_58 = l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25(x_54, x_34, x_57);
lean_dec_ref(x_54);
lean_inc(x_9);
if (x_37 == 0)
{
lean_ctor_set(x_36, 2, x_51);
lean_ctor_set(x_36, 1, x_58);
lean_ctor_set(x_36, 0, x_9);
x_59 = x_36;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_9);
lean_ctor_set(x_69, 1, x_58);
lean_ctor_set(x_69, 2, x_51);
x_59 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_9);
lean_ctor_set(x_60, 1, x_57);
if (x_56 == 0)
{
lean_ctor_set(x_55, 2, x_60);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 0, x_59);
x_61 = x_55;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_60);
x_61 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_62 = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__26___redArg(x_61, x_49);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = 0;
x_65 = l_Lean_addDecl(x_63, x_64, x_48, x_49);
return x_65;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_43);
lean_del_object(x_36);
lean_dec(x_34);
lean_dec(x_9);
x_74 = lean_ctor_get(x_50, 0);
x_81 = !lean_is_exclusive(x_50);
if (x_81 == 0)
{
x_75 = x_50;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_50);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec(x_43);
lean_del_object(x_36);
lean_dec(x_34);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_92 = lean_ctor_get(x_44, 0);
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
x_93 = x_44;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_44);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_del_object(x_36);
lean_dec(x_34);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_100 = lean_ctor_get(x_42, 0);
x_107 = !lean_is_exclusive(x_42);
if (x_107 == 0)
{
x_101 = x_42;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_42);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_111 = lean_ctor_get(x_28, 0);
x_118 = !lean_is_exclusive(x_28);
if (x_118 == 0)
{
x_112 = x_28;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_28);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_119 = l_Lean_MessageData_ofName(x_2);
x_120 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_121, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_122;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
x_16 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_indentD(x_2);
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__1);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__12), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_1);
x_32 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_1, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__4, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__4);
x_36 = l_Lean_MessageData_ofName(x_3);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_1, x_37, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
goto block_31;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_38;
}
}
block_31:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___closed__2);
x_14 = l_Lean_Meta_mapErrorImp___redArg(x_2, x_13, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
x_16 = x_14;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
x_24 = x_14;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0);
x_11 = l_Lean_instInhabitedDefinitionVal_default;
x_12 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
lean_inc(x_1);
x_13 = l_Lean_Name_append(x_1, x_9);
x_14 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__5));
x_15 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__6));
x_16 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__7));
x_17 = lean_box(x_2);
lean_inc(x_13);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___boxed), 14, 9);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_10);
lean_closure_set(x_18, 4, x_14);
lean_closure_set(x_18, 5, x_15);
lean_closure_set(x_18, 6, x_16);
lean_closure_set(x_18, 7, x_17);
lean_closure_set(x_18, 8, x_13);
x_19 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___closed__0));
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__13___boxed), 8, 3);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_13);
x_21 = l_Lean_Meta_realizeConst(x_1, x_13, x_20, x_3, x_4, x_5, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_22 = lean_ctor_get(x_8, 0);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
x_23 = x_8;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__11(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__15(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_5);
x_18 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_8);
x_18 = lean_unbox(x_10);
x_19 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_17, x_9, x_18, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg(x_1, x_2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__38(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_6 = 1;
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Elab_isLatticeTheoretic(x_13);
if (x_14 == 0)
{
x_7 = x_1;
goto block_11;
}
else
{
x_7 = x_5;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__1(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = 1;
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Elab_isPartialFixpoint(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
if (x_4 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
}
else
{
return x_5;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__2(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_6 = 1;
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Elab_isPartialFixpoint(x_13);
if (x_14 == 0)
{
x_7 = x_1;
goto block_11;
}
else
{
x_7 = x_5;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__0(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
x_6 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__4));
x_7 = lean_string_dec_eq(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_8 = 0;
x_9 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__8));
x_10 = lean_string_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__10));
x_12 = lean_string_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_box(0);
x_14 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0));
x_15 = lean_string_dec_eq(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6));
x_17 = lean_string_dec_eq(x_4, x_16);
lean_dec_ref(x_4);
if (x_17 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = 0;
lean_inc(x_3);
x_22 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_5, x_18, x_1, x_3, x_20, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 4);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_23, 7);
lean_inc_ref(x_25);
lean_dec(x_23);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get_borrowed(x_13, x_24, x_34);
x_36 = lean_name_eq(x_35, x_3);
lean_dec(x_3);
if (x_36 == 0)
{
lean_dec_ref(x_24);
x_26 = x_36;
goto block_33;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_array_get_size(x_24);
lean_dec_ref(x_24);
x_39 = lean_nat_dec_lt(x_37, x_38);
x_26 = x_39;
goto block_33;
}
block_33:
{
if (x_26 == 0)
{
lean_dec_ref(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get_size(x_25);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec_ref(x_25);
return x_26;
}
else
{
if (x_29 == 0)
{
lean_dec_ref(x_25);
return x_26;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_28);
x_32 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__0(x_26, x_25, x_30, x_31);
lean_dec_ref(x_25);
if (x_32 == 0)
{
return x_26;
}
else
{
return x_15;
}
}
}
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_3);
return x_15;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec_ref(x_4);
x_40 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = 0;
lean_inc(x_3);
x_44 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_5, x_40, x_1, x_3, x_42, x_43);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_45, 4);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_45, 7);
lean_inc_ref(x_47);
lean_dec(x_45);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_borrowed(x_13, x_46, x_56);
x_58 = lean_name_eq(x_57, x_3);
lean_dec(x_3);
if (x_58 == 0)
{
lean_dec_ref(x_46);
x_48 = x_58;
goto block_55;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_array_get_size(x_46);
lean_dec_ref(x_46);
x_61 = lean_nat_dec_lt(x_59, x_60);
x_48 = x_61;
goto block_55;
}
block_55:
{
if (x_48 == 0)
{
lean_dec_ref(x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_47);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_dec_ref(x_47);
return x_48;
}
else
{
if (x_51 == 0)
{
lean_dec_ref(x_47);
return x_48;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_50);
x_54 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__1(x_48, x_47, x_52, x_53);
lean_dec_ref(x_47);
if (x_54 == 0)
{
return x_48;
}
else
{
return x_12;
}
}
}
}
}
}
else
{
lean_dec(x_44);
lean_dec(x_3);
return x_12;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
lean_dec_ref(x_4);
x_62 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_63, 2);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = 0;
lean_inc(x_3);
x_66 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_5, x_62, x_1, x_3, x_64, x_65);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_ctor_get(x_67, 4);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_67, 7);
lean_inc_ref(x_69);
lean_dec(x_67);
x_70 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_3, x_68);
lean_dec_ref(x_68);
x_71 = lean_box(x_8);
x_72 = lean_array_get(x_71, x_69, x_70);
lean_dec(x_70);
lean_dec_ref(x_69);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
x_74 = l_Lean_Elab_isInductiveFixpoint(x_73);
return x_74;
}
else
{
lean_dec(x_66);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
lean_dec_ref(x_4);
x_75 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_76 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_76, 2);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = 0;
lean_inc(x_3);
x_79 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_5, x_75, x_1, x_3, x_77, x_78);
lean_dec(x_77);
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_80, 7);
lean_inc_ref(x_82);
lean_dec(x_80);
x_83 = l_Array_idxOf___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix_spec__0(x_3, x_81);
lean_dec_ref(x_81);
x_84 = lean_box(x_8);
x_85 = lean_array_get(x_84, x_82, x_83);
lean_dec(x_83);
lean_dec_ref(x_82);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
x_87 = l_Lean_Elab_isCoinductiveFixpoint(x_86);
return x_87;
}
else
{
lean_dec(x_79);
lean_dec(x_3);
return x_7;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
lean_dec_ref(x_4);
x_88 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_89 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = 0;
x_92 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_5, x_88, x_1, x_3, x_90, x_91);
lean_dec(x_90);
if (lean_obj_tag(x_92) == 1)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_ctor_get(x_93, 7);
lean_inc_ref(x_94);
lean_dec(x_93);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_array_get_size(x_94);
x_97 = lean_nat_dec_lt(x_95, x_96);
if (x_97 == 0)
{
lean_dec_ref(x_94);
return x_7;
}
else
{
if (x_97 == 0)
{
lean_dec_ref(x_94);
return x_7;
}
else
{
size_t x_98; size_t x_99; uint8_t x_100; 
x_98 = 0;
x_99 = lean_usize_of_nat(x_96);
x_100 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName_spec__2(x_94, x_98, x_99);
lean_dec_ref(x_94);
if (x_100 == 0)
{
return x_97;
}
else
{
uint8_t x_101; 
x_101 = 0;
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_92);
x_102 = 0;
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_103 = 0;
return x_103;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4);
x_3 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_2 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__0_spec__0_spec__6_spec__29_spec__34_spec__37_spec__38___redArg___closed__4);
x_3 = lean_box(1);
x_4 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_5 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isInductName(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_52; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_61 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__0));
x_62 = lean_string_utf8_byte_size(x_11);
x_63 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_64 = lean_nat_dec_le(x_63, x_62);
if (x_64 == 0)
{
x_52 = x_64;
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_sub(x_62, x_63);
x_67 = lean_string_memcmp(x_11, x_61, x_66, x_65, x_63);
lean_dec(x_66);
if (x_67 == 0)
{
x_52 = x_67;
goto block_60;
}
else
{
lean_dec_ref(x_11);
x_12 = x_7;
goto block_51;
}
}
block_51:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_14 = 0;
x_15 = lean_box(1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_18 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_));
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 1, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 2, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 3, x_7);
x_21 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_22 = lean_st_mk_ref(x_21);
lean_inc(x_22);
x_23 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction(x_10, x_12, x_20, x_22, x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_32; 
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_24 = x_23;
x_25 = x_32;
goto block_31;
}
else
{
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_st_ref_get(x_22);
lean_dec(x_22);
lean_dec(x_26);
x_27 = lean_box(x_7);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_27);
x_28 = x_24;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_41; 
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_23, 0);
lean_dec(x_42);
x_34 = x_23;
x_35 = x_41;
goto block_40;
}
else
{
lean_dec(x_23);
x_34 = lean_box(0);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(x_7);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 0);
lean_ctor_set(x_34, 0, x_36);
x_37 = x_34;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
x_43 = lean_ctor_get(x_23, 0);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
x_44 = x_23;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
block_60:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__6));
x_54 = lean_string_utf8_byte_size(x_11);
x_55 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_56 = lean_nat_dec_le(x_55, x_54);
if (x_56 == 0)
{
lean_dec_ref(x_11);
x_12 = x_52;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_sub(x_54, x_55);
x_59 = lean_string_memcmp(x_11, x_53, x_58, x_57, x_55);
lean_dec(x_58);
lean_dec_ref(x_11);
x_12 = x_59;
goto block_51;
}
}
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_68 = 0;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_));
x_3 = l_Lean_registerReservedNamePredicate(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_3);
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_));
x_5 = l_Lean_registerReservedNameAction(x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__8));
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__0));
x_5 = lean_unsigned_to_nat(327u);
x_6 = lean_unsigned_to_nat(48u);
x_7 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__1));
x_8 = lean_expr_dbg_to_string(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = l_mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_9);
lean_dec_ref(x_9);
x_11 = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__1(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0___closed__1));
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
lean_dec_ref(x_1);
x_7 = l_Lean_Expr_isLambda(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Expr_bindingBody_x21(x_6);
lean_dec_ref(x_6);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__0(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___closed__1));
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Expr_isAppOfArity(x_9, x_10, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isLambda(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec_ref(x_1);
x_1 = x_4;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__0));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(324u);
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj___closed__8));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
x_7 = 0;
lean_inc(x_2);
lean_inc_ref(x_1);
x_8 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_6, x_3, x_1, x_2, x_5, x_7);
lean_dec(x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_borrowed(x_13, x_11, x_14);
x_16 = lean_name_eq(x_2, x_15);
lean_dec(x_2);
if (x_16 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
return x_16;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = l_Lean_Environment_find_x3f(x_1, x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_11);
return x_20;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_ConstantInfo_hasValue(x_22, x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec_ref(x_11);
x_24 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1);
x_25 = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__1(x_24);
x_17 = x_25;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_ConstantInfo_value_x21(x_22, x_20);
lean_dec(x_22);
x_27 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__2(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_11);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_28);
x_29 = l_Lean_Expr_cleanupAnnotations(x_28);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_29);
lean_dec_ref(x_11);
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(x_28, x_31);
lean_dec(x_28);
x_17 = x_32;
goto block_19;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_33);
lean_dec_ref(x_11);
x_35 = lean_box(0);
x_36 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(x_28, x_35);
lean_dec(x_28);
x_17 = x_36;
goto block_19;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_37);
lean_dec_ref(x_11);
x_39 = lean_box(0);
x_40 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(x_28, x_39);
lean_dec(x_28);
x_17 = x_40;
goto block_19;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_41);
x_42 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_11);
x_44 = lean_box(0);
x_45 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(x_28, x_44);
lean_dec(x_28);
x_17 = x_45;
goto block_19;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_47 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__10___closed__15));
x_48 = l_Lean_Expr_isConstOf(x_46, x_47);
lean_dec_ref(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_41);
lean_dec_ref(x_11);
x_49 = lean_box(0);
x_50 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___lam__0(x_28, x_49);
lean_dec(x_28);
x_17 = x_50;
goto block_19;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_28);
x_51 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_52 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_CCPOProdProjs(x_51, x_41);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_14, x_53);
if (x_54 == 0)
{
lean_dec_ref(x_52);
return x_48;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_box(0);
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
if (x_54 == 0)
{
lean_dec_ref(x_52);
return x_48;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_53);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3(x_52, x_57, x_58, x_55);
lean_dec_ref(x_52);
x_17 = x_59;
goto block_19;
}
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_53);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint_spec__3(x_52, x_60, x_61, x_55);
lean_dec_ref(x_52);
x_17 = x_62;
goto block_19;
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
}
block_19:
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
lean_dec_ref(x_17);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__0));
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1));
x_8 = lean_string_dec_eq(x_4, x_7);
lean_dec_ref(x_4);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
x_13 = 0;
lean_inc(x_3);
lean_inc_ref(x_1);
x_14 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_12, x_9, x_1, x_3, x_11, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_16);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_borrowed(x_22, x_16, x_23);
x_25 = lean_name_eq(x_24, x_3);
if (x_25 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
x_17 = x_25;
goto block_21;
}
else
{
uint8_t x_26; 
x_26 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint(x_1, x_3);
x_17 = x_26;
goto block_21;
}
block_21:
{
if (x_17 == 0)
{
lean_dec_ref(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_array_get_size(x_16);
lean_dec_ref(x_16);
x_20 = lean_nat_dec_lt(x_18, x_19);
return x_20;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_4);
x_27 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint(x_1, x_3);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_28 = 0;
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__2);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__3);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__4);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = 0;
x_13 = 1;
x_14 = lean_array_uget_borrowed(x_1, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_inc(x_14);
x_17 = lean_array_push(x_16, x_14);
x_18 = l_Lean_Meta_mkLambdaFVars(x_17, x_4, x_12, x_10, x_12, x_10, x_13, x_5, x_6, x_7, x_8);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_34; 
x_19 = lean_ctor_get(x_18, 0);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
x_20 = x_18;
x_21 = x_34;
goto block_33;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_22; lean_object* x_23; 
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__1));
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 1);
x_23 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_19);
x_23 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5);
x_25 = lean_array_push(x_24, x_23);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_26 = l_Lean_Meta_mkAppOptM(x_22, x_25, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
x_4 = x_27;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_26;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_mkAppN(x_1, x_3);
x_11 = lean_array_get_size(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
x_14 = lean_array_get_borrowed(x_2, x_3, x_13);
lean_dec(x_13);
x_15 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__2));
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_10);
lean_inc(x_14);
x_19 = lean_array_push(x_18, x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_20 = l_Lean_Meta_mkAppM(x_15, x_19, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_mk_empty_array_with_capacity(x_12);
lean_inc(x_14);
x_23 = lean_array_push(x_22, x_14);
x_24 = 0;
x_25 = 1;
x_26 = 1;
x_27 = l_Lean_Meta_mkLambdaFVars(x_23, x_21, x_24, x_25, x_24, x_25, x_26, x_5, x_6, x_7, x_8);
lean_dec_ref(x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_45; 
x_28 = lean_ctor_get(x_27, 0);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
x_29 = x_27;
x_30 = x_45;
goto block_44;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_31; lean_object* x_32; 
x_31 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___closed__4));
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 1);
x_32 = x_29;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_28);
x_32 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0___closed__5);
x_34 = lean_array_push(x_33, x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_35 = l_Lean_Meta_mkAppOptM(x_31, x_34, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_array_pop(x_3);
x_38 = l_Array_reverse___redArg(x_37);
x_39 = lean_array_size(x_38);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm_spec__0(x_38, x_39, x_40, x_36, x_5, x_6, x_7, x_8);
lean_dec_ref(x_38);
return x_41;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_35;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___lam__0___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = 0;
x_12 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(x_8, x_10, x_11, x_2, x_3, x_4, x_5);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_get_size(x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
x_16 = lean_array_get_borrowed(x_1, x_6, x_15);
lean_dec(x_15);
x_17 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___closed__1));
x_18 = lean_mk_empty_array_with_capacity(x_14);
lean_inc(x_16);
lean_inc_ref(x_18);
x_19 = lean_array_push(x_18, x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_20 = l_Lean_Meta_mkAppM(x_17, x_19, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc_ref(x_6);
x_22 = lean_array_pop(x_6);
lean_inc_ref(x_2);
x_23 = l_Lean_mkAppN(x_2, x_22);
lean_dec_ref(x_22);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_24 = l_Lean_Meta_mkEq(x_23, x_21, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_mkAppN(x_3, x_6);
lean_inc(x_11);
lean_inc_ref(x_10);
x_27 = l_Lean_mkArrow(x_25, x_26, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = 1;
x_30 = l_Lean_Meta_mkForallFVars(x_6, x_28, x_4, x_5, x_5, x_29, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_array_push(x_18, x_2);
x_33 = l_Lean_Meta_mkLambdaFVars(x_32, x_31, x_4, x_5, x_4, x_5, x_29, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_32);
return x_33;
}
else
{
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
return x_30;
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_27;
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(x_3);
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__0___boxed), 12, 5);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
x_16 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__4___redArg(x_12, x_15, x_3, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
x_12 = lean_unbox(x_4);
x_13 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__13___closed__1));
lean_inc(x_9);
lean_inc_ref(x_8);
x_15 = l_Lean_Core_mkFreshUserName(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_instInhabitedExpr;
x_18 = 1;
x_19 = lean_array_fget_borrowed(x_2, x_4);
x_20 = lean_box(x_12);
x_21 = lean_box(x_18);
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___lam__1___boxed), 10, 4);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_17);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_21);
x_23 = lean_array_get_borrowed(x_17, x_1, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_23);
x_24 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_16, x_23, x_22, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_3, x_26);
lean_dec(x_3);
x_28 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_29 = lean_array_push(x_5, x_25);
x_3 = x_27;
x_4 = x_28;
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_24, 0);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
x_32 = x_24;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_ctor_get(x_15, 0);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
x_40 = x_15;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_12 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkOptionAdm(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_12, 0);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
x_21 = x_12;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_array_push(x_1, x_4);
x_11 = l_Lean_Level_ofNat(x_2);
x_12 = l_Lean_Expr_sort___override(x_11);
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_10, x_12, x_13, x_3, x_3, x_14, x_5, x_6, x_7, x_8);
lean_dec_ref(x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = lean_whnf(x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_11);
x_21 = l_Lean_Expr_cleanupAnnotations(x_11);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__2));
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
lean_dec_ref(x_24);
if (x_26 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__4));
lean_inc(x_8);
lean_inc_ref(x_7);
x_28 = l_Lean_Core_mkFreshUserName(x_27, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_box(x_2);
x_31 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__0___boxed), 9, 3);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_30);
x_32 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17___redArg(x_29, x_23, x_31, x_5, x_6, x_7, x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_33 = lean_ctor_get(x_28, 0);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
x_34 = x_28;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___closed__1);
x_17 = l_Lean_indentExpr(x_11);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_18, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_19;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_box(x_9);
x_13 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___lam__1___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_array_uget_borrowed(x_3, x_2);
x_15 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_14);
x_16 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRel_spec__0___redArg(x_14, x_13, x_15, x_15, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_uset(x_3, x_2, x_11);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_16, 0);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
x_24 = x_16;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3(x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_fget_borrowed(x_2, x_4);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_13, 0, x_12);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_eq(x_20, x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__0));
x_23 = lean_nat_add(x_4, x_10);
x_24 = l_Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Name_str___override(x_26, x_25);
x_14 = x_27;
goto block_19;
}
else
{
lean_object* x_28; 
x_28 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___closed__1));
x_14 = x_28;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_17 = lean_array_push(x_5, x_15);
x_3 = x_11;
x_4 = x_16;
x_5 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg(x_1, x_2, x_3, x_4, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___lam__0___boxed), 13, 7);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_17);
lean_closure_set(x_18, 6, x_7);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_8, x_9, x_10, x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 0);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
x_21 = x_19;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_28 = lean_ctor_get(x_19, 0);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
x_29 = x_19;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_169; 
x_13 = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__0);
x_14 = l_ReaderT_instMonad___redArg(x_13);
x_15 = lean_ctor_get(x_14, 0);
x_169 = !lean_is_exclusive(x_14);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_14, 1);
lean_dec(x_170);
x_16 = x_14;
x_17 = x_169;
goto block_168;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_166; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 2);
x_20 = lean_ctor_get(x_15, 3);
x_21 = lean_ctor_get(x_15, 4);
x_166 = !lean_is_exclusive(x_15);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_15, 1);
lean_dec(x_167);
x_22 = x_15;
x_23 = x_166;
goto block_165;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__1));
x_25 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__2));
lean_inc_ref(x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_21);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_20);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_31, 0, x_19);
if (x_23 == 0)
{
lean_ctor_set(x_22, 4, x_29);
lean_ctor_set(x_22, 3, x_30);
lean_ctor_set(x_22, 2, x_31);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_28);
x_32 = x_22;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_28);
lean_ctor_set(x_164, 1, x_24);
lean_ctor_set(x_164, 2, x_31);
lean_ctor_set(x_164, 3, x_30);
lean_ctor_set(x_164, 4, x_29);
x_32 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_33; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_32);
x_33 = x_16;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_32);
lean_ctor_set(x_162, 1, x_25);
x_33 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_159; 
x_34 = l_ReaderT_instMonad___redArg(x_33);
x_35 = lean_ctor_get(x_34, 0);
x_159 = !lean_is_exclusive(x_34);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_34, 1);
lean_dec(x_160);
x_36 = x_34;
x_37 = x_159;
goto block_158;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_156; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 2);
x_40 = lean_ctor_get(x_35, 3);
x_41 = lean_ctor_get(x_35, 4);
x_156 = !lean_is_exclusive(x_35);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_35, 1);
lean_dec(x_157);
x_42 = x_35;
x_43 = x_156;
goto block_155;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__3));
x_45 = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__0_spec__0___closed__4));
lean_inc_ref(x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_38);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_41);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_40);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_51, 0, x_39);
if (x_43 == 0)
{
lean_ctor_set(x_42, 4, x_49);
lean_ctor_set(x_42, 3, x_50);
lean_ctor_set(x_42, 2, x_51);
lean_ctor_set(x_42, 1, x_44);
lean_ctor_set(x_42, 0, x_48);
x_52 = x_42;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_154, 0, x_48);
lean_ctor_set(x_154, 1, x_44);
lean_ctor_set(x_154, 2, x_51);
lean_ctor_set(x_154, 3, x_50);
lean_ctor_set(x_154, 4, x_49);
x_52 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_53; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_45);
lean_ctor_set(x_36, 0, x_52);
x_53 = x_36;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_52);
lean_ctor_set(x_152, 1, x_45);
x_53 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_array_get_size(x_7);
x_55 = lean_array_get_size(x_4);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_53);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_mk_empty_array_with_capacity(x_54);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_59 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__0___redArg(x_1, x_7, x_54, x_57, x_58, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_2);
x_61 = l_Array_append___redArg(x_2, x_60);
lean_dec(x_60);
x_62 = lean_array_size(x_61);
x_63 = 0;
x_64 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__1(x_62, x_63, x_61);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_65 = l_Lean_Meta_mkAppOptM(x_3, x_64, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; size_t x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_array_size(x_7);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_68 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__2(x_67, x_63, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = 1;
x_71 = l_Lean_mkAppN(x_66, x_69);
lean_dec(x_69);
x_72 = 1;
x_73 = l_Lean_Meta_mkLambdaFVars(x_7, x_71, x_56, x_70, x_56, x_70, x_72, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = 0;
x_76 = l_Lean_Meta_mkLambdaFVars(x_2, x_74, x_70, x_70, x_56, x_70, x_75, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__5___redArg(x_77, x_9);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9));
x_81 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__3___redArg(x_80, x_10);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_110; 
x_82 = lean_ctor_get(x_81, 0);
x_110 = !lean_is_exclusive(x_81);
if (x_110 == 0)
{
x_83 = x_81;
x_84 = x_110;
goto block_109;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_110;
goto block_109;
}
block_109:
{
uint8_t x_85; 
x_85 = lean_unbox(x_82);
lean_dec(x_82);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (x_84 == 0)
{
lean_ctor_set(x_83, 0, x_79);
x_86 = x_83;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_79);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_del_object(x_83);
x_89 = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___closed__1);
lean_inc(x_79);
x_90 = l_Lean_indentExpr(x_79);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__5(x_80, x_91, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; uint8_t x_99; 
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_92, 0);
lean_dec(x_100);
x_93 = x_92;
x_94 = x_99;
goto block_98;
}
else
{
lean_dec(x_92);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
lean_ctor_set(x_93, 0, x_79);
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_79);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_79);
x_101 = lean_ctor_get(x_92, 0);
x_108 = !lean_is_exclusive(x_92);
if (x_108 == 0)
{
x_102 = x_92;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_92);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec(x_79);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_111 = lean_ctor_get(x_81, 0);
x_118 = !lean_is_exclusive(x_81);
if (x_118 == 0)
{
x_112 = x_81;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_81);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_78;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_76;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
return x_73;
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_66);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_119 = lean_ctor_get(x_68, 0);
x_126 = !lean_is_exclusive(x_68);
if (x_126 == 0)
{
x_120 = x_68;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_68);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_65;
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_134; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_127 = lean_ctor_get(x_59, 0);
x_134 = !lean_is_exclusive(x_59);
if (x_134 == 0)
{
x_128 = x_59;
x_129 = x_134;
goto block_133;
}
else
{
lean_inc(x_127);
lean_dec(x_59);
x_128 = lean_box(0);
x_129 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_130; 
if (x_129 == 0)
{
x_130 = x_128;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_127);
x_130 = x_132;
goto block_131;
}
block_131:
{
return x_130;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_135 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_135, 0, x_53);
x_136 = lean_box(0);
x_137 = 0;
x_138 = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_138, 0, x_135);
x_139 = lean_box(x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_array_get_borrowed(x_141, x_4, x_54);
x_143 = lean_ctor_get(x_142, 1);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_147 = lean_apply_6(x_146, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_unbox(x_145);
x_150 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_144, x_149, x_148, x_5, x_8, x_9, x_10, x_11);
return x_150;
}
else
{
lean_dec(x_144);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_147;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_1, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_9);
x_19 = lean_unbox(x_11);
x_20 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__17_spec__21___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35_spec__41___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6_spec__7(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_18, x_10, x_19, x_12, x_13, x_14, x_15);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___redArg___closed__0));
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16_spec__35___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5_spec__6(x_1, x_2, x_3, x_5, x_6, x_4, x_12, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_size(x_5);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__15(x_12, x_13, x_5);
x_15 = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11_spec__16___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5_spec__5(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_3);
lean_inc_ref(x_7);
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__10___redArg(x_2, x_7, x_1, x_13, x_3, x_14, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_array_size(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_16);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__3(x_17, x_4, x_16, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__4___redArg(x_1, x_19, x_20, x_3, x_21);
lean_dec(x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 0;
x_25 = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__8_spec__11___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness_spec__5(x_16, x_7, x_5, x_6, x_23, x_24, x_8, x_9, x_10, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = lean_ctor_get(x_18, 0);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
x_27 = x_18;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_34 = lean_ctor_get(x_15, 0);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
x_35 = x_15;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_st_ref_get(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = 0;
lean_inc(x_2);
x_19 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_1, x_15, x_14, x_2, x_17, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_115; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 0);
x_115 = !lean_is_exclusive(x_19);
if (x_115 == 0)
{
x_21 = x_19;
x_22 = x_115;
goto block_114;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_20, 4);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_20, 6);
lean_inc_ref(x_24);
lean_dec(x_20);
x_25 = lean_array_size(x_23);
x_26 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_27 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual_spec__1(x_25, x_26, x_23, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_104; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_24);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_borrowed(x_3, x_28, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_32, 1);
x_34 = lean_ctor_get(x_32, 2);
x_104 = !lean_is_exclusive(x_32);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_32, 0);
lean_dec(x_105);
x_35 = x_32;
x_36 = x_104;
goto block_103;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__19___redArg___boxed__const__1));
lean_inc_ref(x_29);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__0___boxed), 12, 6);
lean_closure_set(x_38, 0, x_28);
lean_closure_set(x_38, 1, x_29);
lean_closure_set(x_38, 2, x_30);
lean_closure_set(x_38, 3, x_37);
lean_closure_set(x_38, 4, x_4);
lean_closure_set(x_38, 5, x_5);
x_39 = lean_array_get(x_6, x_29, x_30);
lean_dec_ref(x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_40 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__23___redArg(x_39, x_34, x_38, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_41);
x_42 = lean_infer_type(x_41, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_11);
lean_inc_ref(x_10);
x_44 = l_Lean_Meta_elimOptParam(x_43, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_11);
lean_inc_ref(x_10);
x_46 = l_Lean_Core_betaReduce(x_45, x_10, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_68; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__3);
lean_inc(x_47);
x_49 = l_Lean_collectLevelParams(x_48, x_47);
x_50 = lean_ctor_get(x_49, 2);
x_68 = !lean_is_exclusive(x_49);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_49, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_49, 0);
lean_dec(x_70);
x_51 = x_49;
x_52 = x_68;
goto block_67;
}
else
{
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_box(0);
x_54 = l_List_filterTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__25(x_50, x_33, x_53);
lean_dec_ref(x_50);
lean_inc(x_7);
if (x_36 == 0)
{
lean_ctor_set(x_35, 2, x_47);
lean_ctor_set(x_35, 1, x_54);
lean_ctor_set(x_35, 0, x_7);
x_55 = x_35;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_7);
lean_ctor_set(x_66, 1, x_54);
lean_ctor_set(x_66, 2, x_47);
x_55 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_7);
lean_ctor_set(x_56, 1, x_53);
if (x_52 == 0)
{
lean_ctor_set(x_51, 2, x_56);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 0, x_55);
x_57 = x_51;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_41);
lean_ctor_set(x_64, 2, x_56);
x_57 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_58; 
if (x_22 == 0)
{
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 0, x_57);
x_58 = x_21;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_58 = x_62;
goto block_61;
}
block_61:
{
uint8_t x_59; lean_object* x_60; 
x_59 = 0;
x_60 = l_Lean_addDecl(x_58, x_59, x_10, x_11);
return x_60;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_41);
lean_del_object(x_35);
lean_dec(x_33);
lean_del_object(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
x_71 = lean_ctor_get(x_46, 0);
x_78 = !lean_is_exclusive(x_46);
if (x_78 == 0)
{
x_72 = x_46;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_46);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_41);
lean_del_object(x_35);
lean_dec(x_33);
lean_del_object(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
x_79 = lean_ctor_get(x_44, 0);
x_86 = !lean_is_exclusive(x_44);
if (x_86 == 0)
{
x_80 = x_44;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_44);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_41);
lean_del_object(x_35);
lean_dec(x_33);
lean_del_object(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
x_87 = lean_ctor_get(x_42, 0);
x_94 = !lean_is_exclusive(x_42);
if (x_94 == 0)
{
x_88 = x_42;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_42);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_del_object(x_35);
lean_dec(x_33);
lean_del_object(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_95 = lean_ctor_get(x_40, 0);
x_102 = !lean_is_exclusive(x_40);
if (x_102 == 0)
{
x_96 = x_40;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_40);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec_ref(x_24);
lean_del_object(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_106 = lean_ctor_get(x_27, 0);
x_113 = !lean_is_exclusive(x_27);
if (x_113 == 0)
{
x_107 = x_27;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_27);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_116 = l_Lean_MessageData_ofName(x_2);
x_117 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__11___closed__7);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_mkAdmProj_spec__0___redArg(x_118, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_119;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__1);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction___lam__12), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_st_ref_get(x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
lean_dec(x_34);
x_36 = l_Lean_Environment_contains(x_35, x_2, x_3);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_dec_ref(x_37);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
goto block_33;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_37;
}
}
else
{
lean_dec(x_4);
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_9;
goto block_33;
}
block_33:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__2, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___closed__2);
x_16 = l_Lean_Meta_mapErrorImp___redArg(x_1, x_15, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
x_18 = x_16;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_16, 0);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
x_26 = x_16;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; 
x_8 = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_deriveInduction_spec__21___redArg___closed__0);
x_9 = l_Lean_instInhabitedDefinitionVal_default;
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo_default;
x_12 = 1;
if (x_2 == 0)
{
lean_object* x_27; 
x_27 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__0));
x_22 = x_27;
goto block_26;
}
else
{
lean_object* x_28; 
x_28 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___closed__1));
x_22 = x_28;
goto block_26;
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_1);
x_15 = l_Lean_Name_append(x_1, x_14);
lean_inc(x_13);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__1___boxed), 12, 7);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_9);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_10);
lean_closure_set(x_16, 5, x_8);
lean_closure_set(x_16, 6, x_13);
x_17 = lean_box(x_12);
x_18 = lean_box(x_2);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___lam__3___boxed), 10, 5);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_15);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_1);
lean_closure_set(x_19, 4, x_18);
x_20 = l_Lean_Meta_realizeConst(x_1, x_13, x_19, x_3, x_4, x_5, x_6);
return x_20;
}
block_26:
{
lean_object* x_23; 
lean_inc(x_1);
x_23 = l_Lean_Name_append(x_1, x_22);
if (x_2 == 0)
{
lean_object* x_24; 
x_24 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__5));
x_13 = x_23;
x_14 = x_24;
goto block_21;
}
else
{
lean_object* x_25; 
x_25 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_getInductionPrinciplePostfix___closed__7));
x_13 = x_23;
x_14 = x_25;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_48; lean_object* x_63; uint8_t x_64; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_63 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__0));
x_64 = lean_string_dec_eq(x_6, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1));
x_66 = lean_string_dec_eq(x_6, x_65);
x_48 = x_66;
goto block_62;
}
else
{
x_48 = x_64;
goto block_62;
}
block_47:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_10 = 0;
x_11 = lean_box(1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_14 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_));
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*7 + 1, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*7 + 2, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*7 + 3, x_7);
x_17 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_);
x_18 = lean_st_mk_ref(x_17);
lean_inc(x_18);
x_19 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_derivePartialCorrectness(x_5, x_8, x_16, x_18, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_20 = x_19;
x_21 = x_28;
goto block_27;
}
else
{
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_st_ref_get(x_18);
lean_dec(x_18);
lean_dec(x_22);
x_23 = lean_box(x_10);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_23);
x_24 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_19, 0);
lean_dec(x_38);
x_30 = x_19;
x_31 = x_37;
goto block_36;
}
else
{
lean_dec(x_19);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(x_10);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_39 = lean_ctor_get(x_19, 0);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
x_40 = x_19;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
block_62:
{
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_st_ref_get(x_3);
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
lean_dec(x_51);
lean_inc(x_5);
x_53 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_isOptionFixpoint(x_52, x_5);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_));
x_57 = lean_string_utf8_byte_size(x_6);
x_58 = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_);
x_59 = lean_nat_dec_le(x_58, x_57);
if (x_59 == 0)
{
lean_dec_ref(x_6);
x_7 = x_53;
x_8 = x_59;
goto block_47;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_string_memcmp(x_6, x_56, x_60, x_60, x_58);
lean_dec_ref(x_6);
x_7 = x_53;
x_8 = x_61;
goto block_47;
}
}
}
}
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_67 = 0;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_));
x_3 = l_Lean_registerReservedNamePredicate(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_3);
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_));
x_5 = l_Lean_registerReservedNameAction(x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_unfoldPredRelMutual___closed__9));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Injective(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Internal_Order_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PProdN(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_583250807____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_2457962117____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction_486719255____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Injective(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(builtin);
}
#ifdef __cplusplus
}
#endif
