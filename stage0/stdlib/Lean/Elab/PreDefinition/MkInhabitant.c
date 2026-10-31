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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_9_, lean_object* v_b_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0(v_k_9_, v_b_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(lean_object* v_name_17_, lean_object* v_type_18_, lean_object* v_val_19_, lean_object* v_k_20_, uint8_t v_nondep_21_, uint8_t v_kind_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_28_, 0, v_k_20_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_17_, v_type_18_, v_val_19_, v___f_28_, v_nondep_21_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg___boxed(lean_object* v_name_46_, lean_object* v_type_47_, lean_object* v_val_48_, lean_object* v_k_49_, lean_object* v_nondep_50_, lean_object* v_kind_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_nondep_boxed_57_; uint8_t v_kind_boxed_58_; lean_object* v_res_59_; 
v_nondep_boxed_57_ = lean_unbox(v_nondep_50_);
v_kind_boxed_58_ = lean_unbox(v_kind_51_);
v_res_59_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_46_, v_type_47_, v_val_48_, v_k_49_, v_nondep_boxed_57_, v_kind_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(lean_object* v_00_u03b1_60_, lean_object* v_name_61_, lean_object* v_type_62_, lean_object* v_val_63_, lean_object* v_k_64_, uint8_t v_nondep_65_, uint8_t v_kind_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v_name_61_, v_type_62_, v_val_63_, v_k_64_, v_nondep_65_, v_kind_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___boxed(lean_object* v_00_u03b1_73_, lean_object* v_name_74_, lean_object* v_type_75_, lean_object* v_val_76_, lean_object* v_k_77_, lean_object* v_nondep_78_, lean_object* v_kind_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_nondep_boxed_85_; uint8_t v_kind_boxed_86_; lean_object* v_res_87_; 
v_nondep_boxed_85_ = lean_unbox(v_nondep_78_);
v_kind_boxed_86_ = lean_unbox(v_kind_79_);
v_res_87_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0(v_00_u03b1_73_, v_name_74_, v_type_75_, v_val_76_, v_k_77_, v_nondep_boxed_85_, v_kind_boxed_86_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed(lean_object* v_i_88_, lean_object* v_insts_89_, lean_object* v_xs_90_, lean_object* v_k_91_, lean_object* v_inst_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(v_i_88_, v_insts_89_, v_xs_90_, v_k_91_, v_inst_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v_i_88_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(lean_object* v_xs_109_, lean_object* v_k_110_, lean_object* v_i_111_, lean_object* v_insts_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_get_size(v_xs_109_);
v___x_119_ = lean_nat_dec_lt(v_i_111_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec(v_i_111_);
lean_dec_ref(v_xs_109_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
v___x_120_ = lean_apply_6(v_k_110_, v_insts_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, lean_box(0));
return v___x_120_;
}
else
{
lean_object* v___f_121_; lean_object* v_x_122_; lean_object* v___x_123_; 
lean_inc_ref(v_xs_109_);
lean_inc(v_i_111_);
v___f_121_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_121_, 0, v_i_111_);
lean_closure_set(v___f_121_, 1, v_insts_112_);
lean_closure_set(v___f_121_, 2, v_xs_109_);
lean_closure_set(v___f_121_, 3, v_k_110_);
v_x_122_ = lean_array_fget(v_xs_109_, v_i_111_);
lean_dec(v_i_111_);
lean_dec_ref(v_xs_109_);
lean_inc(v_a_116_);
lean_inc_ref(v_a_115_);
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
lean_inc(v_x_122_);
v___x_123_ = lean_infer_type(v_x_122_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc_n(v_a_124_, 2);
lean_dec_ref_known(v___x_123_, 1);
v___x_125_ = l_Lean_Meta_getLevel(v_a_124_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v___x_125_, 1);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1));
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v_a_126_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_inc_ref(v___x_129_);
v___x_130_ = l_Lean_Expr_const___override(v___x_127_, v___x_129_);
lean_inc(v_a_124_);
v___x_131_ = l_Lean_Expr_app___override(v___x_130_, v_a_124_);
v___x_132_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__3));
v___x_133_ = l_Lean_Expr_const___override(v___x_132_, v___x_129_);
v___x_134_ = l_Lean_mkAppB(v___x_133_, v_a_124_, v_x_122_);
v___x_135_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__5));
v___x_136_ = 0;
v___x_137_ = 0;
v___x_138_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go_spec__0___redArg(v___x_135_, v___x_131_, v___x_134_, v___f_121_, v___x_136_, v___x_137_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_124_);
lean_dec(v_x_122_);
lean_dec_ref(v___f_121_);
v_a_139_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_125_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_125_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_x_122_);
lean_dec_ref(v___f_121_);
v_a_147_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_123_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_123_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___lam__0(lean_object* v_i_155_, lean_object* v_insts_156_, lean_object* v_xs_157_, lean_object* v_k_158_, lean_object* v_inst_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_155_, v___x_165_);
v___x_167_ = lean_array_push(v_insts_156_, v_inst_159_);
v___x_168_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_157_, v_k_158_, v___x_166_, v___x_167_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___boxed(lean_object* v_xs_169_, lean_object* v_k_170_, lean_object* v_i_171_, lean_object* v_insts_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_169_, v_k_170_, v_i_171_, v_insts_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(lean_object* v_00_u03b1_179_, lean_object* v_xs_180_, lean_object* v_k_181_, lean_object* v_i_182_, lean_object* v_insts_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_180_, v_k_181_, v_i_182_, v_insts_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___boxed(lean_object* v_00_u03b1_190_, lean_object* v_xs_191_, lean_object* v_k_192_, lean_object* v_i_193_, lean_object* v_insts_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go(v_00_u03b1_190_, v_xs_191_, v_k_192_, v_i_193_, v_insts_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(lean_object* v_xs_203_, lean_object* v_k_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___closed__0));
v___x_212_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg(v_xs_203_, v_k_204_, v___x_210_, v___x_211_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg___boxed(lean_object* v_xs_213_, lean_object* v_k_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_213_, v_k_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(lean_object* v_00_u03b1_221_, lean_object* v_xs_222_, lean_object* v_k_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_222_, v_k_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___boxed(lean_object* v_00_u03b1_230_, lean_object* v_xs_231_, lean_object* v_k_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances(v_00_u03b1_230_, v_xs_231_, v_k_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(lean_object* v_type_239_, uint8_t v_useOfNonempty_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_a_247_; 
if (v_useOfNonempty_240_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Meta_mkDefault(v_type_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; 
v_a_264_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_254_, 1);
v_a_247_ = v_a_264_;
goto v___jp_246_;
}
}
else
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Meta_mkOfNonempty(v_type_239_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_a_266_);
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
}
else
{
lean_object* v_a_275_; 
v_a_275_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_265_, 1);
v_a_247_ = v_a_275_;
goto v___jp_246_;
}
}
v___jp_246_:
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_Exception_isInterrupt(v_a_247_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
lean_inc_ref(v_a_247_);
v___x_249_ = l_Lean_Exception_isRuntime(v_a_247_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_a_247_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_a_247_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v_a_247_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f___boxed(lean_object* v_type_276_, lean_object* v_useOfNonempty_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
uint8_t v_useOfNonempty_boxed_283_; lean_object* v_res_284_; 
v_useOfNonempty_boxed_283_ = lean_unbox(v_useOfNonempty_277_);
v_res_284_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_276_, v_useOfNonempty_boxed_283_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(lean_object* v_k_285_, lean_object* v_b_286_, lean_object* v_c_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
v___x_293_ = lean_apply_7(v_k_285_, v_b_286_, v_c_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, lean_box(0));
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_k_294_, lean_object* v_b_295_, lean_object* v_c_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0(v_k_294_, v_b_295_, v_c_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(lean_object* v_type_303_, lean_object* v_k_304_, uint8_t v_cleanupAnnotations_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___f_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_311_, 0, v_k_304_);
v___x_312_ = 0;
v___x_313_ = lean_box(0);
v___x_314_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_312_, v___x_313_, v_type_303_, v___f_311_, v_cleanupAnnotations_305_, v___x_312_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_a_323_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_314_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_314_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg___boxed(lean_object* v_type_331_, lean_object* v_k_332_, lean_object* v_cleanupAnnotations_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_339_; lean_object* v_res_340_; 
v_cleanupAnnotations_boxed_339_ = lean_unbox(v_cleanupAnnotations_333_);
v_res_340_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_331_, v_k_332_, v_cleanupAnnotations_boxed_339_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(lean_object* v_00_u03b1_341_, lean_object* v_type_342_, lean_object* v_k_343_, uint8_t v_cleanupAnnotations_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_type_342_, v_k_343_, v_cleanupAnnotations_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___boxed(lean_object* v_00_u03b1_351_, lean_object* v_type_352_, lean_object* v_k_353_, lean_object* v_cleanupAnnotations_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_360_; lean_object* v_res_361_; 
v_cleanupAnnotations_boxed_360_ = lean_unbox(v_cleanupAnnotations_354_);
v_res_361_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0(v_00_u03b1_351_, v_type_352_, v_k_353_, v_cleanupAnnotations_boxed_360_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = l_Lean_maxRecDepthErrorMessage;
v___x_368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__3);
v___x_370_ = l_Lean_MessageData_ofFormat(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__4);
v___x_372_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__2));
v___x_373_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(lean_object* v_ref_374_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___closed__5);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_ref_374_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg___boxed(lean_object* v_ref_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_ref_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_383_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___boxed(lean_object* v_00_u03b1_390_, lean_object* v_ref_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1(v_00_u03b1_390_, v_ref_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed(lean_object* v_xs_398_, lean_object* v_insts_399_, lean_object* v_useOfNonempty_400_, lean_object* v_xs_x27_401_, lean_object* v_type_x27_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v_useOfNonempty_boxed_408_; lean_object* v_res_409_; 
v_useOfNonempty_boxed_408_ = lean_unbox(v_useOfNonempty_400_);
v_res_409_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(v_xs_398_, v_insts_399_, v_useOfNonempty_boxed_408_, v_xs_x27_401_, v_type_x27_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(lean_object* v_xs_410_, lean_object* v_insts_411_, lean_object* v_type_412_, uint8_t v_useOfNonempty_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_toCold_419_; lean_object* v_currRecDepth_420_; lean_object* v_ref_421_; uint16_t v_optionFlags_422_; uint8_t v_suppressElabErrors_423_; uint8_t v_checkDeprecated_424_; uint8_t v_isRecordingDeps_425_; lean_object* v_maxRecDepth_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_toCold_419_ = lean_ctor_get(v_a_416_, 0);
lean_inc_ref(v_toCold_419_);
v_currRecDepth_420_ = lean_ctor_get(v_a_416_, 1);
lean_inc(v_currRecDepth_420_);
v_ref_421_ = lean_ctor_get(v_a_416_, 2);
lean_inc(v_ref_421_);
v_optionFlags_422_ = lean_ctor_get_uint16(v_a_416_, sizeof(void*)*3);
v_suppressElabErrors_423_ = lean_ctor_get_uint8(v_a_416_, sizeof(void*)*3 + 2);
v_checkDeprecated_424_ = lean_ctor_get_uint8(v_a_416_, sizeof(void*)*3 + 3);
v_isRecordingDeps_425_ = lean_ctor_get_uint8(v_a_416_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_416_);
v_maxRecDepth_426_ = lean_ctor_get(v_toCold_419_, 3);
v___x_427_ = lean_box(v_useOfNonempty_413_);
lean_inc_ref(v_insts_411_);
lean_inc_ref(v_xs_410_);
v___f_428_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1___boxed), 10, 3);
lean_closure_set(v___f_428_, 0, v_xs_410_);
lean_closure_set(v___f_428_, 1, v_insts_411_);
lean_closure_set(v___f_428_, 2, v___x_427_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_nat_dec_eq(v_maxRecDepth_426_, v___x_498_);
if (v___x_499_ == 0)
{
uint8_t v___x_500_; 
v___x_500_ = lean_nat_dec_eq(v_currRecDepth_420_, v_maxRecDepth_426_);
if (v___x_500_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v___x_501_; 
lean_dec_ref(v___f_428_);
lean_dec(v_currRecDepth_420_);
lean_dec_ref(v_toCold_419_);
lean_dec_ref(v_type_412_);
lean_dec_ref(v_insts_411_);
lean_dec_ref(v_xs_410_);
v___x_501_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__1___redArg(v_ref_421_);
return v___x_501_;
}
}
else
{
goto v___jp_429_;
}
v___jp_429_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_currRecDepth_420_, v___x_430_);
lean_dec(v_currRecDepth_420_);
v___x_432_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_432_, 0, v_toCold_419_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
lean_ctor_set(v___x_432_, 2, v_ref_421_);
lean_ctor_set_uint16(v___x_432_, sizeof(void*)*3, v_optionFlags_422_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*3 + 2, v_suppressElabErrors_423_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*3 + 3, v_checkDeprecated_424_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*3 + 4, v_isRecordingDeps_425_);
lean_inc_ref(v_type_412_);
v___x_433_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitant_x3f(v_type_412_, v_useOfNonempty_413_, v_a_414_, v_a_415_, v___x_432_, v_a_417_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
if (lean_obj_tag(v_a_434_) == 1)
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v___f_428_);
lean_dec_ref(v_type_412_);
v_val_435_ = lean_ctor_get(v_a_434_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_a_434_);
if (v_isSharedCheck_472_ == 0)
{
v___x_437_ = v_a_434_;
v_isShared_438_ = v_isSharedCheck_472_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v_a_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_472_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = 1;
v___x_440_ = 1;
v___x_441_ = l_Lean_Meta_mkLetFVars(v_insts_411_, v_val_435_, v___x_439_, v___x_439_, v___x_440_, v_a_414_, v_a_415_, v___x_432_, v_a_417_);
lean_dec_ref(v_insts_411_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; uint8_t v___x_443_; lean_object* v___x_444_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = 0;
v___x_444_ = l_Lean_Meta_mkLambdaFVars(v_xs_410_, v_a_442_, v___x_443_, v___x_439_, v___x_443_, v___x_439_, v___x_440_, v_a_414_, v_a_415_, v___x_432_, v_a_417_);
lean_dec_ref_known(v___x_432_, 3);
lean_dec_ref(v_xs_410_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_455_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_a_445_);
v___x_450_ = v___x_437_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_437_);
v_a_456_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_444_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_444_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_del_object(v___x_437_);
lean_dec_ref_known(v___x_432_, 3);
lean_dec_ref(v_xs_410_);
v_a_464_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_441_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_441_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
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
}
else
{
lean_object* v___x_473_; 
lean_dec(v_a_434_);
v___x_473_ = l_Lean_Meta_whnfCore(v_type_412_, v_a_414_, v_a_415_, v___x_432_, v_a_417_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; uint8_t v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v___x_475_ = l_Lean_Expr_isForall(v_a_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec_ref(v___f_428_);
v___x_476_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_474_, v___x_475_, v_a_414_, v_a_415_, v___x_432_, v_a_417_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
if (lean_obj_tag(v_a_477_) == 1)
{
lean_object* v_val_481_; 
lean_del_object(v___x_479_);
v_val_481_ = lean_ctor_get(v_a_477_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v_a_477_, 1);
v_type_412_ = v_val_481_;
v_a_416_ = v___x_432_;
goto _start;
}
else
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_a_477_);
lean_dec_ref_known(v___x_432_, 3);
lean_dec_ref(v_insts_411_);
lean_dec_ref(v_xs_410_);
v___x_483_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_483_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec_ref_known(v___x_432_, 3);
lean_dec_ref(v_insts_411_);
lean_dec_ref(v_xs_410_);
return v___x_476_;
}
}
else
{
uint8_t v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v_insts_411_);
lean_dec_ref(v_xs_410_);
v___x_488_ = 0;
v___x_489_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f_spec__0___redArg(v_a_474_, v___f_428_, v___x_488_, v_a_414_, v_a_415_, v___x_432_, v_a_417_);
lean_dec_ref_known(v___x_432_, 3);
return v___x_489_;
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref_known(v___x_432_, 3);
lean_dec_ref(v___f_428_);
lean_dec_ref(v_insts_411_);
lean_dec_ref(v_xs_410_);
v_a_490_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_473_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_473_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_432_, 3);
lean_dec_ref(v___f_428_);
lean_dec_ref(v_type_412_);
lean_dec_ref(v_insts_411_);
lean_dec_ref(v_xs_410_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(lean_object* v_xs_502_, lean_object* v_xs_x27_503_, lean_object* v_insts_504_, lean_object* v_type_x27_505_, uint8_t v_useOfNonempty_506_, lean_object* v_insts_x27_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = l_Array_append___redArg(v_xs_502_, v_xs_x27_503_);
v___x_514_ = l_Array_append___redArg(v_insts_504_, v_insts_x27_507_);
lean_inc_ref(v___y_510_);
v___x_515_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v___x_513_, v___x_514_, v_type_x27_505_, v_useOfNonempty_506_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed(lean_object* v_xs_516_, lean_object* v_xs_x27_517_, lean_object* v_insts_518_, lean_object* v_type_x27_519_, lean_object* v_useOfNonempty_520_, lean_object* v_insts_x27_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v_useOfNonempty_boxed_527_; lean_object* v_res_528_; 
v_useOfNonempty_boxed_527_ = lean_unbox(v_useOfNonempty_520_);
v_res_528_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0(v_xs_516_, v_xs_x27_517_, v_insts_518_, v_type_x27_519_, v_useOfNonempty_boxed_527_, v_insts_x27_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v_insts_x27_521_);
lean_dec_ref(v_xs_x27_517_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__1(lean_object* v_xs_529_, lean_object* v_insts_530_, uint8_t v_useOfNonempty_531_, lean_object* v_xs_x27_532_, lean_object* v_type_x27_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v___x_539_ = lean_box(v_useOfNonempty_531_);
lean_inc_ref(v_xs_x27_532_);
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_540_, 0, v_xs_529_);
lean_closure_set(v___f_540_, 1, v_xs_x27_532_);
lean_closure_set(v___f_540_, 2, v_insts_530_);
lean_closure_set(v___f_540_, 3, v_type_x27_533_);
lean_closure_set(v___f_540_, 4, v___x_539_);
v___x_541_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_x27_532_, v___f_540_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f___boxed(lean_object* v_xs_542_, lean_object* v_insts_543_, lean_object* v_type_544_, lean_object* v_useOfNonempty_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
uint8_t v_useOfNonempty_boxed_551_; lean_object* v_res_552_; 
v_useOfNonempty_boxed_551_ = lean_unbox(v_useOfNonempty_545_);
v_res_552_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_542_, v_insts_543_, v_type_544_, v_useOfNonempty_boxed_551_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(lean_object* v_msgData_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v_env_560_; uint8_t v___x_561_; lean_object* v_env_562_; lean_object* v___x_563_; lean_object* v_toCold_564_; lean_object* v_mctx_565_; lean_object* v_lctx_566_; lean_object* v_options_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_559_ = lean_st_ref_get(v___y_557_);
v_env_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref(v_env_560_);
lean_dec(v___x_559_);
v___x_561_ = 0;
v_env_562_ = l_Lean_Environment_setRecordingDeps(v_env_560_, v___x_561_);
v___x_563_ = lean_st_ref_get(v___y_555_);
v_toCold_564_ = lean_ctor_get(v___y_556_, 0);
v_mctx_565_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_mctx_565_);
lean_dec(v___x_563_);
v_lctx_566_ = lean_ctor_get(v___y_554_, 2);
v_options_567_ = lean_ctor_get(v_toCold_564_, 2);
lean_inc_ref(v_options_567_);
lean_inc_ref(v_lctx_566_);
v___x_568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_568_, 0, v_env_562_);
lean_ctor_set(v___x_568_, 1, v_mctx_565_);
lean_ctor_set(v___x_568_, 2, v_lctx_566_);
lean_ctor_set(v___x_568_, 3, v_options_567_);
v___x_569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_msgData_553_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0___boxed(lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msgData_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_ref_584_; lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_ref_584_ = lean_ctor_get(v___y_581_, 2);
v___x_585_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0_spec__0(v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_inc(v_ref_584_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_ref_584_);
lean_ctor_set(v___x_590_, 1, v_a_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg___boxed(lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__0));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__2));
v___x_607_ = l_Lean_stringToMessageData(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4(void){
_start:
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = 0;
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances_go___redArg___closed__1));
v___x_610_ = l_Lean_MessageData_ofConstName(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__5));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9(void){
_start:
{
uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = 0;
v___x_618_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__8));
v___x_619_ = l_Lean_MessageData_ofConstName(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__10));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Elab_mkInhabitantFor___lam__0___closed__12));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0(lean_object* v_xs_626_, lean_object* v_type_627_, lean_object* v_failedToMessage_628_, lean_object* v_insts_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_635_; lean_object* v___x_636_; 
v___x_635_ = 0;
lean_inc_ref(v___y_632_);
lean_inc_ref(v_type_627_);
lean_inc_ref(v_insts_629_);
lean_inc_ref(v_xs_626_);
v___x_636_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_626_, v_insts_629_, v_type_627_, v___x_635_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_685_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_685_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_685_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_685_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
if (lean_obj_tag(v_a_637_) == 0)
{
uint8_t v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_639_);
v___x_641_ = 1;
lean_inc_ref(v___y_632_);
lean_inc_ref(v_type_627_);
lean_inc_ref(v_xs_626_);
v___x_642_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_mkInhabitantForAux_x3f(v_xs_626_, v_insts_629_, v_type_627_, v___x_641_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_672_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_672_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_672_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_672_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
if (lean_obj_tag(v_a_643_) == 1)
{
lean_object* v_val_647_; lean_object* v___x_649_; 
lean_dec_ref(v_failedToMessage_628_);
lean_dec_ref(v_type_627_);
lean_dec_ref(v_xs_626_);
v_val_647_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_a_643_, 1);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_val_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_val_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
uint8_t v___x_651_; lean_object* v___x_652_; 
lean_del_object(v___x_645_);
lean_dec(v_a_643_);
v___x_651_ = 1;
v___x_652_ = l_Lean_Meta_mkForallFVars(v_xs_626_, v_type_627_, v___x_635_, v___x_641_, v___x_641_, v___x_651_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec_ref(v_xs_626_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__1, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__1_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__1);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v_failedToMessage_628_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_indentExpr(v_a_653_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__3, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__3_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__3);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__4, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__4_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__4);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__6, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__6_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__6);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__9, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__9_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__9);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__11, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__11_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__11);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_660_);
v___x_669_ = lean_obj_once(&l_Lean_Elab_mkInhabitantFor___lam__0___closed__13, &l_Lean_Elab_mkInhabitantFor___lam__0___closed__13_once, _init_l_Lean_Elab_mkInhabitantFor___lam__0___closed__13);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v___x_670_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
return v___x_671_;
}
else
{
lean_dec_ref(v_failedToMessage_628_);
return v___x_652_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_failedToMessage_628_);
lean_dec_ref(v_type_627_);
lean_dec_ref(v_xs_626_);
v_a_673_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_642_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_642_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
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
else
{
lean_object* v_val_681_; lean_object* v___x_683_; 
lean_dec_ref(v_insts_629_);
lean_dec_ref(v_failedToMessage_628_);
lean_dec_ref(v_type_627_);
lean_dec_ref(v_xs_626_);
v_val_681_ = lean_ctor_get(v_a_637_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v_a_637_, 1);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_val_681_);
v___x_683_ = v___x_639_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_val_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_insts_629_);
lean_dec_ref(v_failedToMessage_628_);
lean_dec_ref(v_type_627_);
lean_dec_ref(v_xs_626_);
v_a_686_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_636_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_636_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___lam__0___boxed(lean_object* v_xs_694_, lean_object* v_type_695_, lean_object* v_failedToMessage_696_, lean_object* v_insts_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_mkInhabitantFor___lam__0(v_xs_694_, v_type_695_, v_failedToMessage_696_, v_insts_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor(lean_object* v_failedToMessage_704_, lean_object* v_xs_705_, lean_object* v_type_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; 
lean_inc_ref(v_xs_705_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Elab_mkInhabitantFor___lam__0___boxed), 9, 3);
lean_closure_set(v___f_712_, 0, v_xs_705_);
lean_closure_set(v___f_712_, 1, v_type_706_);
lean_closure_set(v___f_712_, 2, v_failedToMessage_704_);
v___x_713_ = l___private_Lean_Elab_PreDefinition_MkInhabitant_0__Lean_Elab_withInhabitedInstances___redArg(v_xs_705_, v___f_712_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInhabitantFor___boxed(lean_object* v_failedToMessage_714_, lean_object* v_xs_715_, lean_object* v_type_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Elab_mkInhabitantFor(v_failedToMessage_714_, v_xs_715_, v_type_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(lean_object* v_00_u03b1_723_, lean_object* v_msg_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___redArg(v_msg_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0___boxed(lean_object* v_00_u03b1_731_, lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwError___at___00Lean_Elab_mkInhabitantFor_spec__0(v_00_u03b1_731_, v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_738_;
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
