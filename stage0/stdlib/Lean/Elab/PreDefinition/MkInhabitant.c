// Lean compiler output
// Module: Lean.Elab.PreDefinition.MkInhabitant
// Imports: public import Lean.Meta.AppBuilder public import Lean.PrettyPrinter import Init.Omega
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(108, 140, 114, 129, 213, 60, 200, 249)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ", could not prove that the type"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 137, .m_capacity = 137, .m_length = 136, .m_data = "\nis nonempty.\n\nThis process uses multiple strategies:\n- It looks for a parameter that matches the return type.\n- It tries synthesizing '"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' and '"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "' instances for the return type, while making every parameter into a local '"};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__11;
static const lean_string_object l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 182, .m_capacity = 182, .m_length = 181, .m_data = "' instance.\n- It tries unfolding the return type.\n\nIf the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it."};
static const lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_mkInhabitantFor___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_6(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_9_;
v_res_9_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(lean_object* v_name_18_, lean_object* v_type_19_, lean_object* v_val_20_, lean_object* v_k_21_, uint8_t v_nondep_22_, uint8_t v_kind_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_29_, 0, v_k_21_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_18_, v_type_19_, v_val_20_, v___f_29_, v_nondep_22_, v_kind_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_18_ = stack[0].m_obj;
lean_object* v_type_19_ = stack[1].m_obj;
lean_object* v_val_20_ = stack[2].m_obj;
lean_object* v_k_21_ = stack[3].m_obj;
uint8_t v_nondep_22_ = stack[4].m_num;
uint8_t v_kind_23_ = stack[5].m_num;
lean_object* v___y_24_ = stack[6].m_obj;
lean_object* v___y_25_ = stack[7].m_obj;
lean_object* v___y_26_ = stack[8].m_obj;
lean_object* v___y_27_ = stack[9].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_18_, v_type_19_, v_val_20_, v_k_21_, v_nondep_22_, v_kind_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___boxed(lean_object* v_name_48_, lean_object* v_type_49_, lean_object* v_val_50_, lean_object* v_k_51_, lean_object* v_nondep_52_, lean_object* v_kind_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
uint8_t v_nondep_boxed_59_; uint8_t v_kind_boxed_60_; lean_object* v_res_61_; 
v_nondep_boxed_59_ = lean_unbox(v_nondep_52_);
v_kind_boxed_60_ = lean_unbox(v_kind_53_);
v_res_61_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_48_, v_type_49_, v_val_50_, v_k_51_, v_nondep_boxed_59_, v_kind_boxed_60_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_61_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(lean_object* v_00_u03b1_62_, lean_object* v_name_63_, lean_object* v_type_64_, lean_object* v_val_65_, lean_object* v_k_66_, uint8_t v_nondep_67_, uint8_t v_kind_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_63_, v_type_64_, v_val_65_, v_k_66_, v_nondep_67_, v_kind_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_63_ = stack[1].m_obj;
lean_object* v_type_64_ = stack[2].m_obj;
lean_object* v_val_65_ = stack[3].m_obj;
lean_object* v_k_66_ = stack[4].m_obj;
uint8_t v_nondep_67_ = stack[5].m_num;
uint8_t v_kind_68_ = stack[6].m_num;
lean_object* v___y_69_ = stack[7].m_obj;
lean_object* v___y_70_ = stack[8].m_obj;
lean_object* v___y_71_ = stack[9].m_obj;
lean_object* v___y_72_ = stack[10].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(lean_box(0), v_name_63_, v_type_64_, v_val_65_, v_k_66_, v_nondep_67_, v_kind_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(lean_object* v_00_u03b1_76_, lean_object* v_name_77_, lean_object* v_type_78_, lean_object* v_val_79_, lean_object* v_k_80_, lean_object* v_nondep_81_, lean_object* v_kind_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
uint8_t v_nondep_boxed_88_; uint8_t v_kind_boxed_89_; lean_object* v_res_90_; 
v_nondep_boxed_88_ = lean_unbox(v_nondep_81_);
v_kind_boxed_89_ = lean_unbox(v_kind_82_);
v_res_90_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(v_00_u03b1_76_, v_name_77_, v_type_78_, v_val_79_, v_k_80_, v_nondep_boxed_88_, v_kind_boxed_89_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(lean_object* v_i_91_, lean_object* v_insts_92_, lean_object* v_xs_93_, lean_object* v_k_94_, lean_object* v_inst_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_91_, v_insts_92_, v_xs_93_, v_k_94_, v_inst_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v_i_91_);
return v_res_101_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(lean_object* v_xs_112_, lean_object* v_k_113_, lean_object* v_i_114_, lean_object* v_insts_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_get_size(v_xs_112_);
v___x_122_ = lean_nat_dec_lt(v_i_114_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_dec(v_i_114_);
lean_dec_ref(v_xs_112_);
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
v___x_123_ = lean_apply_6(v_k_113_, v_insts_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, lean_box(0));
return v___x_123_;
}
else
{
lean_object* v___f_124_; lean_object* v_x_125_; lean_object* v___x_126_; 
lean_inc_ref(v_xs_112_);
lean_inc(v_i_114_);
v___f_124_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_124_, 0, v_i_114_);
lean_closure_set(v___f_124_, 1, v_insts_115_);
lean_closure_set(v___f_124_, 2, v_xs_112_);
lean_closure_set(v___f_124_, 3, v_k_113_);
v_x_125_ = lean_array_fget(v_xs_112_, v_i_114_);
lean_dec(v_i_114_);
lean_dec_ref(v_xs_112_);
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_x_125_);
v___x_126_ = lean_infer_type(v_x_125_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_n(v_a_127_, 2);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = l_Lean_Meta_getLevel(v_a_127_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v___x_130_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1));
v___x_131_ = lean_box(0);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v_a_129_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_inc_ref(v___x_132_);
v___x_133_ = l_Lean_Expr_const___override(v___x_130_, v___x_132_);
lean_inc(v_a_127_);
v___x_134_ = l_Lean_Expr_app___override(v___x_133_, v_a_127_);
v___x_135_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3));
v___x_136_ = l_Lean_Expr_const___override(v___x_135_, v___x_132_);
v___x_137_ = l_Lean_mkAppB(v___x_136_, v_a_127_, v_x_125_);
v___x_138_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5));
v___x_139_ = 0;
v___x_140_ = 0;
v___x_141_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v___x_138_, v___x_134_, v___x_137_, v___f_124_, v___x_139_, v___x_140_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
return v___x_141_;
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_a_127_);
lean_dec(v_x_125_);
lean_dec_ref(v___f_124_);
v_a_142_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_128_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_128_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v_x_125_);
lean_dec_ref(v___f_124_);
v_a_150_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_126_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_126_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_112_ = stack[0].m_obj;
lean_object* v_k_113_ = stack[1].m_obj;
lean_object* v_i_114_ = stack[2].m_obj;
lean_object* v_insts_115_ = stack[3].m_obj;
lean_object* v_a_116_ = stack[4].m_obj;
lean_object* v_a_117_ = stack[5].m_obj;
lean_object* v_a_118_ = stack[6].m_obj;
lean_object* v_a_119_ = stack[7].m_obj;
lean_object* v_res_158_;
v_res_158_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_112_, v_k_113_, v_i_114_, v_insts_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
stack->m_obj
 = v_res_158_;
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(lean_object* v_i_159_, lean_object* v_insts_160_, lean_object* v_xs_161_, lean_object* v_k_162_, lean_object* v_inst_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_i_159_, v___x_169_);
v___x_171_ = lean_array_push(v_insts_160_, v_inst_163_);
v___x_172_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_161_, v_k_162_, v___x_170_, v___x_171_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
return v___x_172_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_159_ = stack[0].m_obj;
lean_object* v_insts_160_ = stack[1].m_obj;
lean_object* v_xs_161_ = stack[2].m_obj;
lean_object* v_k_162_ = stack[3].m_obj;
lean_object* v_inst_163_ = stack[4].m_obj;
lean_object* v___y_164_ = stack[5].m_obj;
lean_object* v___y_165_ = stack[6].m_obj;
lean_object* v___y_166_ = stack[7].m_obj;
lean_object* v___y_167_ = stack[8].m_obj;
lean_object* v_res_173_;
v_res_173_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_159_, v_insts_160_, v_xs_161_, v_k_162_, v_inst_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(lean_object* v_xs_174_, lean_object* v_k_175_, lean_object* v_i_176_, lean_object* v_insts_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_174_, v_k_175_, v_i_176_, v_insts_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_183_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(lean_object* v_00_u03b1_184_, lean_object* v_xs_185_, lean_object* v_k_186_, lean_object* v_i_187_, lean_object* v_insts_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_185_, v_k_186_, v_i_187_, v_insts_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_194_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_185_ = stack[1].m_obj;
lean_object* v_k_186_ = stack[2].m_obj;
lean_object* v_i_187_ = stack[3].m_obj;
lean_object* v_insts_188_ = stack[4].m_obj;
lean_object* v_a_189_ = stack[5].m_obj;
lean_object* v_a_190_ = stack[6].m_obj;
lean_object* v_a_191_ = stack[7].m_obj;
lean_object* v_a_192_ = stack[8].m_obj;
lean_object* v_res_195_;
v_res_195_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(lean_box(0), v_xs_185_, v_k_186_, v_i_187_, v_insts_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(lean_object* v_00_u03b1_196_, lean_object* v_xs_197_, lean_object* v_k_198_, lean_object* v_i_199_, lean_object* v_insts_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(v_00_u03b1_196_, v_xs_197_, v_k_198_, v_i_199_, v_insts_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
return v_res_206_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(lean_object* v_xs_209_, lean_object* v_k_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0));
v___x_218_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_209_, v_k_210_, v___x_216_, v___x_217_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_218_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_209_ = stack[0].m_obj;
lean_object* v_k_210_ = stack[1].m_obj;
lean_object* v_a_211_ = stack[2].m_obj;
lean_object* v_a_212_ = stack[3].m_obj;
lean_object* v_a_213_ = stack[4].m_obj;
lean_object* v_a_214_ = stack[5].m_obj;
lean_object* v_res_219_;
v_res_219_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_209_, v_k_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(lean_object* v_xs_220_, lean_object* v_k_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_220_, v_k_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(lean_object* v_00_u03b1_228_, lean_object* v_xs_229_, lean_object* v_k_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_229_, v_k_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
return v___x_236_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_229_ = stack[1].m_obj;
lean_object* v_k_230_ = stack[2].m_obj;
lean_object* v_a_231_ = stack[3].m_obj;
lean_object* v_a_232_ = stack[4].m_obj;
lean_object* v_a_233_ = stack[5].m_obj;
lean_object* v_a_234_ = stack[6].m_obj;
lean_object* v_res_237_;
v_res_237_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(lean_box(0), v_xs_229_, v_k_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(lean_object* v_00_u03b1_238_, lean_object* v_xs_239_, lean_object* v_k_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(v_00_u03b1_238_, v_xs_239_, v_k_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_246_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object* v_type_247_, uint8_t v_useOfNonempty_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v_a_261_; 
if (v_useOfNonempty_248_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_mkDefault(v_type_247_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_273_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_273_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_273_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_a_265_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_271_ = v___x_267_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_a_274_; 
v_a_274_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_264_, 1);
v_a_261_ = v_a_274_;
goto v___jp_260_;
}
}
else
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_mkOfNonempty(v_type_247_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_284_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v_a_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v_a_285_; 
v_a_285_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_275_, 1);
v_a_261_ = v_a_285_;
goto v___jp_260_;
}
}
v___jp_254_:
{
if (v___y_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v___y_255_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v___y_255_);
return v___x_259_;
}
}
v___jp_260_:
{
uint8_t v___x_262_; 
v___x_262_ = l_Lean_Exception_isInterrupt(v_a_261_);
if (v___x_262_ == 0)
{
uint8_t v___x_263_; 
lean_inc_ref(v_a_261_);
v___x_263_ = l_Lean_Exception_isRuntime(v_a_261_);
v___y_255_ = v_a_261_;
v___y_256_ = v___x_263_;
goto v___jp_254_;
}
else
{
v___y_255_ = v_a_261_;
v___y_256_ = v___x_262_;
goto v___jp_254_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_247_ = stack[0].m_obj;
uint8_t v_useOfNonempty_248_ = stack[1].m_num;
lean_object* v_a_249_ = stack[2].m_obj;
lean_object* v_a_250_ = stack[3].m_obj;
lean_object* v_a_251_ = stack[4].m_obj;
lean_object* v_a_252_ = stack[5].m_obj;
lean_object* v_res_286_;
v_res_286_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_247_, v_useOfNonempty_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object* v_type_287_, lean_object* v_useOfNonempty_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
uint8_t v_useOfNonempty_boxed_294_; lean_object* v_res_295_; 
v_useOfNonempty_boxed_294_ = lean_unbox(v_useOfNonempty_288_);
v_res_295_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_287_, v_useOfNonempty_boxed_294_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_295_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(lean_object* v_k_296_, lean_object* v_b_297_, lean_object* v_c_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
v___x_304_ = lean_apply_7(v_k_296_, v_b_297_, v_c_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, lean_box(0));
return v___x_304_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_296_ = stack[0].m_obj;
lean_object* v_b_297_ = stack[1].m_obj;
lean_object* v_c_298_ = stack[2].m_obj;
lean_object* v___y_299_ = stack[3].m_obj;
lean_object* v___y_300_ = stack[4].m_obj;
lean_object* v___y_301_ = stack[5].m_obj;
lean_object* v___y_302_ = stack[6].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_296_, v_b_297_, v_c_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_k_306_, lean_object* v_b_307_, lean_object* v_c_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_306_, v_b_307_, v_c_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(lean_object* v_type_315_, lean_object* v_k_316_, uint8_t v_cleanupAnnotations_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___f_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___f_323_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_323_, 0, v_k_316_);
v___x_324_ = 0;
v___x_325_ = lean_box(0);
v___x_326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_324_, v___x_325_, v_type_315_, v___f_323_, v_cleanupAnnotations_317_, v___x_324_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_a_335_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_326_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_326_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_315_ = stack[0].m_obj;
lean_object* v_k_316_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_317_ = stack[2].m_num;
lean_object* v___y_318_ = stack[3].m_obj;
lean_object* v___y_319_ = stack[4].m_obj;
lean_object* v___y_320_ = stack[5].m_obj;
lean_object* v___y_321_ = stack[6].m_obj;
lean_object* v_res_343_;
v_res_343_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_315_, v_k_316_, v_cleanupAnnotations_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___boxed(lean_object* v_type_344_, lean_object* v_k_345_, lean_object* v_cleanupAnnotations_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_352_; lean_object* v_res_353_; 
v_cleanupAnnotations_boxed_352_ = lean_unbox(v_cleanupAnnotations_346_);
v_res_353_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_344_, v_k_345_, v_cleanupAnnotations_boxed_352_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_353_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(lean_object* v_00_u03b1_354_, lean_object* v_type_355_, lean_object* v_k_356_, uint8_t v_cleanupAnnotations_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_355_, v_k_356_, v_cleanupAnnotations_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_355_ = stack[1].m_obj;
lean_object* v_k_356_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_357_ = stack[3].m_num;
lean_object* v___y_358_ = stack[4].m_obj;
lean_object* v___y_359_ = stack[5].m_obj;
lean_object* v___y_360_ = stack[6].m_obj;
lean_object* v___y_361_ = stack[7].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(lean_box(0), v_type_355_, v_k_356_, v_cleanupAnnotations_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_type_366_, lean_object* v_k_367_, lean_object* v_cleanupAnnotations_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_374_; lean_object* v_res_375_; 
v_cleanupAnnotations_boxed_374_ = lean_unbox(v_cleanupAnnotations_368_);
v_res_375_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(v_00_u03b1_365_, v_type_366_, v_k_367_, v_cleanupAnnotations_boxed_374_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_375_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = l_Lean_maxRecDepthErrorMessage;
v___x_382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3);
v___x_384_ = l_Lean_MessageData_ofFormat(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4);
v___x_386_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2));
v___x_387_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
return v___x_387_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(lean_object* v_ref_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_388_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_388_ = stack[0].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_388_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(lean_object* v_ref_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_394_);
return v_res_396_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(lean_object* v_00_u03b1_397_, lean_object* v_ref_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_398_);
return v___x_404_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_398_ = stack[1].m_obj;
lean_object* v___y_399_ = stack[2].m_obj;
lean_object* v___y_400_ = stack[3].m_obj;
lean_object* v___y_401_ = stack[4].m_obj;
lean_object* v___y_402_ = stack[5].m_obj;
lean_object* v_res_405_;
v_res_405_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(lean_box(0), v_ref_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(lean_object* v_00_u03b1_406_, lean_object* v_ref_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(v_00_u03b1_406_, v_ref_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(lean_object* v_xs_414_, lean_object* v_insts_415_, lean_object* v_useOfNonempty_416_, lean_object* v_xs_x27_417_, lean_object* v_type_x27_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v_useOfNonempty_boxed_424_; lean_object* v_res_425_; 
v_useOfNonempty_boxed_424_ = lean_unbox(v_useOfNonempty_416_);
v_res_425_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_414_, v_insts_415_, v_useOfNonempty_boxed_424_, v_xs_x27_417_, v_type_x27_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_425_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(lean_object* v_xs_426_, lean_object* v_insts_427_, lean_object* v_type_428_, uint8_t v_useOfNonempty_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_toCold_435_; lean_object* v_currRecDepth_436_; lean_object* v_ref_437_; uint16_t v_optionFlags_438_; uint8_t v_suppressElabErrors_439_; uint8_t v_isRecordingDeps_440_; lean_object* v_maxRecDepth_441_; lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_toCold_435_ = lean_ctor_get(v_a_432_, 0);
lean_inc_ref(v_toCold_435_);
v_currRecDepth_436_ = lean_ctor_get(v_a_432_, 1);
lean_inc(v_currRecDepth_436_);
v_ref_437_ = lean_ctor_get(v_a_432_, 2);
lean_inc(v_ref_437_);
v_optionFlags_438_ = lean_ctor_get_uint16(v_a_432_, sizeof(void*)*3);
v_suppressElabErrors_439_ = lean_ctor_get_uint8(v_a_432_, sizeof(void*)*3 + 2);
v_isRecordingDeps_440_ = lean_ctor_get_uint8(v_a_432_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_432_);
v_maxRecDepth_441_ = lean_ctor_get(v_toCold_435_, 3);
v___x_442_ = lean_box(v_useOfNonempty_429_);
lean_inc_ref(v_insts_427_);
lean_inc_ref(v_xs_426_);
v___f_443_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed), 10, 3);
lean_closure_set(v___f_443_, 0, v_xs_426_);
lean_closure_set(v___f_443_, 1, v_insts_427_);
lean_closure_set(v___f_443_, 2, v___x_442_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_nat_dec_eq(v_maxRecDepth_441_, v___x_513_);
if (v___x_514_ == 0)
{
uint8_t v___x_515_; 
v___x_515_ = lean_nat_dec_eq(v_currRecDepth_436_, v_maxRecDepth_441_);
if (v___x_515_ == 0)
{
goto v___jp_444_;
}
else
{
lean_object* v___x_516_; 
lean_dec_ref(v___f_443_);
lean_dec(v_currRecDepth_436_);
lean_dec_ref(v_toCold_435_);
lean_dec_ref(v_type_428_);
lean_dec_ref(v_insts_427_);
lean_dec_ref(v_xs_426_);
v___x_516_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_437_);
return v___x_516_;
}
}
else
{
goto v___jp_444_;
}
v___jp_444_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_currRecDepth_436_, v___x_445_);
lean_dec(v_currRecDepth_436_);
v___x_447_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_447_, 0, v_toCold_435_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
lean_ctor_set(v___x_447_, 2, v_ref_437_);
lean_ctor_set_uint16(v___x_447_, sizeof(void*)*3, v_optionFlags_438_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 2, v_suppressElabErrors_439_);
lean_ctor_set_uint8(v___x_447_, sizeof(void*)*3 + 3, v_isRecordingDeps_440_);
lean_inc_ref(v_type_428_);
v___x_448_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_428_, v_useOfNonempty_429_, v_a_430_, v_a_431_, v___x_447_, v_a_433_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
if (lean_obj_tag(v_a_449_) == 1)
{
lean_object* v_val_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v___f_443_);
lean_dec_ref(v_type_428_);
v_val_450_ = lean_ctor_get(v_a_449_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_487_ == 0)
{
v___x_452_ = v_a_449_;
v_isShared_453_ = v_isSharedCheck_487_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_val_450_);
lean_dec(v_a_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_487_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v___x_454_ = 1;
v___x_455_ = 1;
v___x_456_ = l_Lean_Meta_mkLetFVars(v_insts_427_, v_val_450_, v___x_454_, v___x_454_, v___x_455_, v_a_430_, v_a_431_, v___x_447_, v_a_433_);
lean_dec_ref(v_insts_427_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; uint8_t v___x_458_; lean_object* v___x_459_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = 0;
v___x_459_ = l_Lean_Meta_mkLambdaFVars(v_xs_426_, v_a_457_, v___x_458_, v___x_454_, v___x_458_, v___x_454_, v___x_455_, v_a_430_, v_a_431_, v___x_447_, v_a_433_);
lean_dec_ref_known(v___x_447_, 3);
lean_dec_ref(v_xs_426_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_470_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_470_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_470_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_470_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_a_460_);
v___x_465_ = v___x_452_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_452_);
v_a_471_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_459_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_459_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_del_object(v___x_452_);
lean_dec_ref_known(v___x_447_, 3);
lean_dec_ref(v_xs_426_);
v_a_479_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_456_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_456_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_a_449_);
v___x_488_ = l_Lean_Meta_whnfCore(v_type_428_, v_a_430_, v_a_431_, v___x_447_, v_a_433_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; uint8_t v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = l_Lean_Expr_isForall(v_a_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec_ref(v___f_443_);
v___x_491_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_489_, v___x_490_, v_a_430_, v_a_431_, v___x_447_, v_a_433_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_502_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_502_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_502_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
if (lean_obj_tag(v_a_492_) == 1)
{
lean_object* v_val_496_; 
lean_del_object(v___x_494_);
v_val_496_ = lean_ctor_get(v_a_492_, 0);
lean_inc(v_val_496_);
lean_dec_ref_known(v_a_492_, 1);
v_type_428_ = v_val_496_;
v_a_432_ = v___x_447_;
goto _start;
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v_a_492_);
lean_dec_ref_known(v___x_447_, 3);
lean_dec_ref(v_insts_427_);
lean_dec_ref(v_xs_426_);
v___x_498_ = lean_box(0);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_498_);
v___x_500_ = v___x_494_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_447_, 3);
lean_dec_ref(v_insts_427_);
lean_dec_ref(v_xs_426_);
return v___x_491_;
}
}
else
{
uint8_t v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_insts_427_);
lean_dec_ref(v_xs_426_);
v___x_503_ = 0;
v___x_504_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_a_489_, v___f_443_, v___x_503_, v_a_430_, v_a_431_, v___x_447_, v_a_433_);
lean_dec_ref_known(v___x_447_, 3);
return v___x_504_;
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref_known(v___x_447_, 3);
lean_dec_ref(v___f_443_);
lean_dec_ref(v_insts_427_);
lean_dec_ref(v_xs_426_);
v_a_505_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_488_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_488_);
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
else
{
lean_dec_ref_known(v___x_447_, 3);
lean_dec_ref(v___f_443_);
lean_dec_ref(v_type_428_);
lean_dec_ref(v_insts_427_);
lean_dec_ref(v_xs_426_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_426_ = stack[0].m_obj;
lean_object* v_insts_427_ = stack[1].m_obj;
lean_object* v_type_428_ = stack[2].m_obj;
uint8_t v_useOfNonempty_429_ = stack[3].m_num;
lean_object* v_a_430_ = stack[4].m_obj;
lean_object* v_a_431_ = stack[5].m_obj;
lean_object* v_a_432_ = stack[6].m_obj;
lean_object* v_a_433_ = stack[7].m_obj;
lean_object* v_res_517_;
v_res_517_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_426_, v_insts_427_, v_type_428_, v_useOfNonempty_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
stack->m_obj
 = v_res_517_;
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(lean_object* v_xs_518_, lean_object* v_xs_x27_519_, lean_object* v_insts_520_, lean_object* v_type_x27_521_, uint8_t v_useOfNonempty_522_, lean_object* v_insts_x27_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = l_Array_append___redArg(v_xs_518_, v_xs_x27_519_);
v___x_530_ = l_Array_append___redArg(v_insts_520_, v_insts_x27_523_);
lean_inc_ref(v___y_526_);
v___x_531_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v___x_529_, v___x_530_, v_type_x27_521_, v_useOfNonempty_522_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
return v___x_531_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_518_ = stack[0].m_obj;
lean_object* v_xs_x27_519_ = stack[1].m_obj;
lean_object* v_insts_520_ = stack[2].m_obj;
lean_object* v_type_x27_521_ = stack[3].m_obj;
uint8_t v_useOfNonempty_522_ = stack[4].m_num;
lean_object* v_insts_x27_523_ = stack[5].m_obj;
lean_object* v___y_524_ = stack[6].m_obj;
lean_object* v___y_525_ = stack[7].m_obj;
lean_object* v___y_526_ = stack[8].m_obj;
lean_object* v___y_527_ = stack[9].m_obj;
lean_object* v_res_532_;
v_res_532_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_518_, v_xs_x27_519_, v_insts_520_, v_type_x27_521_, v_useOfNonempty_522_, v_insts_x27_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed(lean_object* v_xs_533_, lean_object* v_xs_x27_534_, lean_object* v_insts_535_, lean_object* v_type_x27_536_, lean_object* v_useOfNonempty_537_, lean_object* v_insts_x27_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
uint8_t v_useOfNonempty_boxed_544_; lean_object* v_res_545_; 
v_useOfNonempty_boxed_544_ = lean_unbox(v_useOfNonempty_537_);
v_res_545_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_533_, v_xs_x27_534_, v_insts_535_, v_type_x27_536_, v_useOfNonempty_boxed_544_, v_insts_x27_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_insts_x27_538_);
lean_dec_ref(v_xs_x27_534_);
return v_res_545_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(lean_object* v_xs_546_, lean_object* v_insts_547_, uint8_t v_useOfNonempty_548_, lean_object* v_xs_x27_549_, lean_object* v_type_x27_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(v_useOfNonempty_548_);
lean_inc_ref(v_xs_x27_549_);
v___f_557_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_557_, 0, v_xs_546_);
lean_closure_set(v___f_557_, 1, v_xs_x27_549_);
lean_closure_set(v___f_557_, 2, v_insts_547_);
lean_closure_set(v___f_557_, 3, v_type_x27_550_);
lean_closure_set(v___f_557_, 4, v___x_556_);
v___x_558_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_x27_549_, v___f_557_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_558_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_546_ = stack[0].m_obj;
lean_object* v_insts_547_ = stack[1].m_obj;
uint8_t v_useOfNonempty_548_ = stack[2].m_num;
lean_object* v_xs_x27_549_ = stack[3].m_obj;
lean_object* v_type_x27_550_ = stack[4].m_obj;
lean_object* v___y_551_ = stack[5].m_obj;
lean_object* v___y_552_ = stack[6].m_obj;
lean_object* v___y_553_ = stack[7].m_obj;
lean_object* v___y_554_ = stack[8].m_obj;
lean_object* v_res_559_;
v_res_559_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_546_, v_insts_547_, v_useOfNonempty_548_, v_xs_x27_549_, v_type_x27_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(lean_object* v_xs_560_, lean_object* v_insts_561_, lean_object* v_type_562_, lean_object* v_useOfNonempty_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
uint8_t v_useOfNonempty_boxed_569_; lean_object* v_res_570_; 
v_useOfNonempty_boxed_569_ = lean_unbox(v_useOfNonempty_563_);
v_res_570_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_560_, v_insts_561_, v_type_562_, v_useOfNonempty_boxed_569_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_570_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v_env_578_; uint8_t v___x_579_; lean_object* v_env_580_; lean_object* v___x_581_; lean_object* v_toCold_582_; lean_object* v_mctx_583_; lean_object* v_lctx_584_; lean_object* v_options_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_577_ = lean_st_ref_get(v___y_575_);
v_env_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_577_);
v___x_579_ = 0;
v_env_580_ = l_Lean_Environment_setRecordingDeps(v_env_578_, v___x_579_);
v___x_581_ = lean_st_ref_get(v___y_573_);
v_toCold_582_ = lean_ctor_get(v___y_574_, 0);
v_mctx_583_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_mctx_583_);
lean_dec(v___x_581_);
v_lctx_584_ = lean_ctor_get(v___y_572_, 2);
v_options_585_ = lean_ctor_get(v_toCold_582_, 2);
lean_inc_ref(v_options_585_);
lean_inc_ref(v_lctx_584_);
v___x_586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_586_, 0, v_env_580_);
lean_ctor_set(v___x_586_, 1, v_mctx_583_);
lean_ctor_set(v___x_586_, 2, v_lctx_584_);
lean_ctor_set(v___x_586_, 3, v_options_585_);
v___x_587_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_msgData_571_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_571_ = stack[0].m_obj;
lean_object* v___y_572_ = stack[1].m_obj;
lean_object* v___y_573_ = stack[2].m_obj;
lean_object* v___y_574_ = stack[3].m_obj;
lean_object* v___y_575_ = stack[4].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
stack->m_obj
 = v_res_589_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(lean_object* v_msgData_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_596_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_ref_603_; lean_object* v___x_604_; lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_ref_603_ = lean_ctor_get(v___y_600_, 2);
v___x_604_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_inc(v_ref_603_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_ref_603_);
lean_ctor_set(v___x_609_, 1, v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_597_ = stack[0].m_obj;
lean_object* v___y_598_ = stack[1].m_obj;
lean_object* v___y_599_ = stack[2].m_obj;
lean_object* v___y_600_ = stack[3].m_obj;
lean_object* v___y_601_ = stack[4].m_obj;
lean_object* v_res_614_;
v_res_614_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg___boxed(lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__0));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__2));
v___x_627_ = l_Lean_stringToMessageData(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4(void){
_start:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = 0;
v___x_629_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1));
v___x_630_ = l_Lean_MessageData_ofConstName(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__5));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9(void){
_start:
{
uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = 0;
v___x_638_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__8));
v___x_639_ = l_Lean_MessageData_ofConstName(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__10));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__12));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
lean_object* l_Lean_Elab_mkInhabitantFor___lam__0(lean_object* v_xs_646_, lean_object* v_type_647_, lean_object* v_failedToMessage_648_, lean_object* v_insts_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
uint8_t v___x_655_; lean_object* v___y_657_; lean_object* v___x_697_; 
v___x_655_ = 0;
lean_inc_ref(v___y_652_);
lean_inc_ref(v_type_647_);
lean_inc_ref(v_insts_649_);
lean_inc_ref(v_xs_646_);
v___x_697_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_646_, v_insts_649_, v_type_647_, v___x_655_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
if (lean_obj_tag(v_a_698_) == 0)
{
uint8_t v___x_699_; lean_object* v___x_700_; 
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = 1;
lean_inc_ref(v___y_652_);
lean_inc_ref(v_type_647_);
lean_inc_ref(v_xs_646_);
v___x_700_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_646_, v_insts_649_, v_type_647_, v___x_699_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
v___y_657_ = v___x_700_;
goto v___jp_656_;
}
else
{
lean_dec_ref(v_insts_649_);
v___y_657_ = v___x_697_;
goto v___jp_656_;
}
}
else
{
lean_dec_ref(v_insts_649_);
v___y_657_ = v___x_697_;
goto v___jp_656_;
}
v___jp_656_:
{
if (lean_obj_tag(v___y_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_688_; 
v_a_658_ = lean_ctor_get(v___y_657_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___y_657_);
if (v_isSharedCheck_688_ == 0)
{
v___x_660_ = v___y_657_;
v_isShared_661_ = v_isSharedCheck_688_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___y_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_688_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
if (lean_obj_tag(v_a_658_) == 1)
{
lean_object* v_val_662_; lean_object* v___x_664_; 
lean_dec_ref(v_failedToMessage_648_);
lean_dec_ref(v_type_647_);
lean_dec_ref(v_xs_646_);
v_val_662_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_a_658_, 1);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_val_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_val_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
uint8_t v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; 
lean_del_object(v___x_660_);
lean_dec(v_a_658_);
v___x_666_ = 1;
v___x_667_ = 1;
v___x_668_ = l_Lean_Meta_mkForallFVars(v_xs_646_, v_type_647_, v___x_655_, v___x_666_, v___x_666_, v___x_667_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec_ref(v_xs_646_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__1, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v_failedToMessage_648_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_indentExpr(v_a_669_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__3, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__4, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__6, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__9, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__11, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_676_);
v___x_685_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__13, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v___x_686_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
return v___x_687_;
}
else
{
lean_dec_ref(v_failedToMessage_648_);
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_failedToMessage_648_);
lean_dec_ref(v_type_647_);
lean_dec_ref(v_xs_646_);
v_a_689_ = lean_ctor_get(v___y_657_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___y_657_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___y_657_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___y_657_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_mkInhabitantFor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_646_ = stack[0].m_obj;
lean_object* v_type_647_ = stack[1].m_obj;
lean_object* v_failedToMessage_648_ = stack[2].m_obj;
lean_object* v_insts_649_ = stack[3].m_obj;
lean_object* v___y_650_ = stack[4].m_obj;
lean_object* v___y_651_ = stack[5].m_obj;
lean_object* v___y_652_ = stack[6].m_obj;
lean_object* v___y_653_ = stack[7].m_obj;
lean_object* v_res_701_;
v_res_701_ = l_Lean_Elab_mkInhabitantFor___lam__0(v_xs_646_, v_type_647_, v_failedToMessage_648_, v_insts_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___boxed(lean_object* v_xs_702_, lean_object* v_type_703_, lean_object* v_failedToMessage_704_, lean_object* v_insts_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_mkInhabitantFor___lam__0(v_xs_702_, v_type_703_, v_failedToMessage_704_, v_insts_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object* v_failedToMessage_712_, lean_object* v_xs_713_, lean_object* v_type_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___f_720_; lean_object* v___x_721_; 
lean_inc_ref(v_xs_713_);
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Elab_mkInhabitantFor___lam__0___boxed), 9, 3);
lean_closure_set(v___f_720_, 0, v_xs_713_);
lean_closure_set(v___f_720_, 1, v_type_714_);
lean_closure_set(v___f_720_, 2, v_failedToMessage_712_);
v___x_721_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_713_, v___f_720_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_721_;
}
}
LEAN_EXPORT void l_Lean_Elab_mkInhabitantFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_failedToMessage_712_ = stack[0].m_obj;
lean_object* v_xs_713_ = stack[1].m_obj;
lean_object* v_type_714_ = stack[2].m_obj;
lean_object* v_a_715_ = stack[3].m_obj;
lean_object* v_a_716_ = stack[4].m_obj;
lean_object* v_a_717_ = stack[5].m_obj;
lean_object* v_a_718_ = stack[6].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Lean_Elab_mkInhabitantFor(v_failedToMessage_712_, v_xs_713_, v_type_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___boxed(lean_object* v_failedToMessage_723_, lean_object* v_xs_724_, lean_object* v_type_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Elab_mkInhabitantFor(v_failedToMessage_723_, v_xs_724_, v_type_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
return v_res_731_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(lean_object* v_00_u03b1_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v___x_739_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_733_ = stack[1].m_obj;
lean_object* v___y_734_ = stack[2].m_obj;
lean_object* v___y_735_ = stack[3].m_obj;
lean_object* v___y_736_ = stack[4].m_obj;
lean_object* v___y_737_ = stack[5].m_obj;
lean_object* v_res_740_;
v_res_740_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(lean_box(0), v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___boxed(lean_object* v_00_u03b1_741_, lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(v_00_u03b1_741_, v_msg_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_748_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
}
#ifdef __cplusplus
}
#endif
