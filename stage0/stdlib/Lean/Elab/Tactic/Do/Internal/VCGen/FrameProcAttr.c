// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.FrameProcAttr
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown constant '"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "VCGen"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FrameProc"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 166, 206, 84, 210, 155, 104)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 214, 136, 164, 237, 239, 105, 243)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value_aux_5),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__8_value),LEAN_SCALAR_PTR_LITERAL(22, 137, 234, 103, 66, 6, 216, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a `FrameProc`"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_toFrameProcEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_toFrameProcEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "frameProcExt"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 166, 206, 84, 210, 155, 104)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 214, 136, 164, 237, 239, 105, 243)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 14, 177, 96, 81, 72, 167, 133)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_frameProcExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "frameproc"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 4, 63, 122, 93, 234, 142, 166)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(132, 236, 244, 1, 128, 181, 211, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(175, 167, 22, 210, 240, 170, 245, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "FrameProcAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 138, 190, 118, 160, 53, 150, 205)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(25, 96, 223, 156, 157, 203, 57, 14)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 82, 161, 51, 180, 176, 235, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(54, 13, 78, 242, 219, 52, 111, 88)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(203, 139, 206, 150, 182, 111, 249, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(23, 54, 56, 121, 79, 17, 54, 101)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(194, 20, 167, 212, 207, 133, 189, 161)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(25, 120, 179, 227, 57, 137, 26, 214)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 71, 55, 5, 121, 183, 172, 9)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 1, 183, 4, 118, 97, 220, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(68, 135, 119, 79, 58, 41, 45, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(94, 224, 58, 58, 144, 206, 32, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(131, 43, 253, 2, 209, 235, 126, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 100, 107, 247, 140, 251, 186, 168)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(42, 54, 116, 77, 43, 20, 12, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 100, 248, 246, 81, 232, 39)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 116, 204, 107, 21, 124, 255, 98)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1192303900) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(31, 15, 191, 128, 140, 42, 9, 213)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 24, 74, 29, 112, 233, 102, 7)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 63, 158, 200, 180, 255, 106, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(17, 178, 215, 48, 11, 247, 177, 254)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__1_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "register a frame inference procedure for `vcgen`"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(lean_object* v_e_1_){
_start:
{
if (lean_obj_tag(v_e_1_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_a_3_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_e_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v_e_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_mk_io_user_error(v_a_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set_tag(v___x_5_, 1);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_a_12_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v_e_1_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_e_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 0);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0(lean_object* v_00_u03b1_23_, lean_object* v_e_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_27_, lean_object* v_e_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0(v_00_u03b1_27_, v_e_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl(lean_object* v_declName_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_env_53_; lean_object* v_opts_54_; uint8_t v___x_55_; lean_object* v___x_56_; 
v_env_53_ = lean_ctor_get(v_a_51_, 0);
v_opts_54_ = lean_ctor_get(v_a_51_, 1);
v___x_55_ = 0;
lean_inc(v_declName_50_);
lean_inc_ref(v_env_53_);
v___x_56_ = l_Lean_Environment_find_x3f(v_env_53_, v_declName_50_, v___x_55_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_57_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__0));
v___x_58_ = 1;
v___x_59_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_50_, v___x_58_);
v___x_60_ = lean_string_append(v___x_57_, v___x_59_);
lean_dec_ref(v___x_59_);
v___x_61_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__1));
v___x_62_ = lean_string_append(v___x_60_, v___x_61_);
v___x_63_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_84_; 
v_val_65_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_84_ == 0)
{
v___x_67_ = v___x_56_;
v_isShared_68_ = v_isSharedCheck_84_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_val_65_);
lean_dec(v___x_56_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_84_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = l_Lean_ConstantInfo_type(v_val_65_);
lean_dec(v_val_65_);
v___x_70_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__9));
v___x_71_ = l_Lean_Expr_isConstOf(v___x_69_, v___x_70_);
lean_dec_ref(v___x_69_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_72_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__10));
v___x_73_ = 1;
v___x_74_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_50_, v___x_73_);
v___x_75_ = lean_string_append(v___x_72_, v___x_74_);
lean_dec_ref(v___x_74_);
v___x_76_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___closed__11));
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 18);
lean_ctor_set(v___x_67_, 0, v___x_77_);
v___x_79_ = v___x_67_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_del_object(v___x_67_);
v___x_82_ = l_Lean_Environment_evalConst___redArg(v_env_53_, v_opts_54_, v_declName_50_, v___x_71_);
lean_dec(v_declName_50_);
v___x_83_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v___x_82_);
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl___boxed(lean_object* v_declName_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl(v_declName_85_, v_a_86_);
lean_dec_ref(v_a_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_toFrameProcEntry(lean_object* v_declName_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v_declName_89_);
v___x_92_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl(v_declName_89_, v_a_90_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_101_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_declName_89_);
lean_ctor_set(v___x_97_, 1, v_a_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_97_);
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_declName_89_);
v_a_102_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_92_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_toFrameProcEntry___boxed(lean_object* v_declName_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_toFrameProcEntry(v_declName_110_, v_a_111_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v___y_114_){
_start:
{
lean_inc_ref(v___y_114_);
return v___y_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___y_115_);
lean_dec_ref(v___y_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_a_118_);
lean_inc_ref_n(v___x_119_, 2);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_121_, v_a_122_);
lean_dec_ref(v_x_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_s_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_snd_126_; lean_object* v___x_127_; 
v_snd_126_ = lean_ctor_get(v_x_125_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v_x_125_);
v___x_127_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert(v_s_124_, v_snd_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_128_){
_start:
{
lean_object* v_fst_129_; 
v_fst_129_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_fst_129_);
return v_fst_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_130_);
lean_dec_ref(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_132_, lean_object* v_declName_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_toFrameProcEntry(v_declName_133_, v___y_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_137_, lean_object* v_declName_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_137_, v_declName_138_, v___y_139_);
lean_dec_ref(v___y_139_);
lean_dec_ref(v_x_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v___x_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v___x_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___x_145_);
return v_res_147_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = lean_unsigned_to_nat(16u);
v___x_164_ = lean_mk_array(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_168_; lean_object* v___f_169_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___f_169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v___x_168_);
return v___f_169_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___f_170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_175_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___x_177_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___f_175_);
lean_ctor_set(v___x_177_, 2, v___f_174_);
lean_ctor_set(v___x_177_, 3, v___f_173_);
lean_ctor_set(v___x_177_, 4, v___f_172_);
lean_ctor_set(v___x_177_, 5, v___f_171_);
lean_ctor_set(v___x_177_, 6, v___f_170_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_180_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg___lam__0(lean_object* v___x_183_, lean_object* v_toPure_184_, lean_object* v_____do__lift_185_){
_start:
{
lean_object* v___x_186_; lean_object* v_ext_187_; lean_object* v_toEnvExtension_188_; lean_object* v_asyncMode_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_186_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_frameProcExt;
v_ext_187_ = lean_ctor_get(v___x_186_, 1);
v_toEnvExtension_188_ = lean_ctor_get(v_ext_187_, 0);
v_asyncMode_189_ = lean_ctor_get(v_toEnvExtension_188_, 2);
v___x_190_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_183_, v___x_186_, v_____do__lift_185_, v_asyncMode_189_);
v___x_191_ = lean_apply_2(v_toPure_184_, lean_box(0), v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg___lam__0___boxed(lean_object* v___x_192_, lean_object* v_toPure_193_, lean_object* v_____do__lift_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg___lam__0(v___x_192_, v_toPure_193_, v_____do__lift_194_);
lean_dec_ref(v___x_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg(lean_object* v_inst_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v_toApplicative_198_; lean_object* v_toBind_199_; lean_object* v_getEnv_200_; lean_object* v_toPure_201_; lean_object* v___x_202_; lean_object* v___f_203_; lean_object* v___x_204_; 
v_toApplicative_198_ = lean_ctor_get(v_inst_196_, 0);
lean_inc_ref(v_toApplicative_198_);
v_toBind_199_ = lean_ctor_get(v_inst_196_, 1);
lean_inc(v_toBind_199_);
lean_dec_ref(v_inst_196_);
v_getEnv_200_ = lean_ctor_get(v_inst_197_, 0);
lean_inc(v_getEnv_200_);
lean_dec_ref(v_inst_197_);
v_toPure_201_ = lean_ctor_get(v_toApplicative_198_, 1);
lean_inc(v_toPure_201_);
lean_dec_ref(v_toApplicative_198_);
v___x_202_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs;
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_203_, 0, v___x_202_);
lean_closure_set(v___f_203_, 1, v_toPure_201_);
v___x_204_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v_getEnv_200_, v___f_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs(lean_object* v_m_205_, lean_object* v_inst_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcs___redArg(v_inst_206_, v_inst_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_209_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__0);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__1);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg(lean_object* v_ext_214_, lean_object* v_b_215_, uint8_t v_kind_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_currNamespace_220_; lean_object* v___x_221_; lean_object* v_env_222_; lean_object* v_nextMacroScope_223_; lean_object* v_ngen_224_; lean_object* v_auxDeclNGen_225_; lean_object* v_traceState_226_; lean_object* v_messages_227_; lean_object* v_infoState_228_; lean_object* v_snapshotTasks_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_241_; 
v_currNamespace_220_ = lean_ctor_get(v___y_217_, 6);
v___x_221_ = lean_st_ref_take(v___y_218_);
v_env_222_ = lean_ctor_get(v___x_221_, 0);
v_nextMacroScope_223_ = lean_ctor_get(v___x_221_, 1);
v_ngen_224_ = lean_ctor_get(v___x_221_, 2);
v_auxDeclNGen_225_ = lean_ctor_get(v___x_221_, 3);
v_traceState_226_ = lean_ctor_get(v___x_221_, 4);
v_messages_227_ = lean_ctor_get(v___x_221_, 6);
v_infoState_228_ = lean_ctor_get(v___x_221_, 7);
v_snapshotTasks_229_ = lean_ctor_get(v___x_221_, 8);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; 
v_unused_242_ = lean_ctor_get(v___x_221_, 5);
lean_dec(v_unused_242_);
v___x_231_ = v___x_221_;
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snapshotTasks_229_);
lean_inc(v_infoState_228_);
lean_inc(v_messages_227_);
lean_inc(v_traceState_226_);
lean_inc(v_auxDeclNGen_225_);
lean_inc(v_ngen_224_);
lean_inc(v_nextMacroScope_223_);
lean_inc(v_env_222_);
lean_dec(v___x_221_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
lean_inc(v_currNamespace_220_);
v___x_233_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_222_, v_ext_214_, v_b_215_, v_kind_216_, v_currNamespace_220_);
v___x_234_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___closed__2);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 5, v___x_234_);
lean_ctor_set(v___x_231_, 0, v___x_233_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_nextMacroScope_223_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_ngen_224_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_auxDeclNGen_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_traceState_226_);
lean_ctor_set(v_reuseFailAlloc_240_, 5, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_240_, 6, v_messages_227_);
lean_ctor_set(v_reuseFailAlloc_240_, 7, v_infoState_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 8, v_snapshotTasks_229_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_st_ref_set(v___y_218_, v___x_236_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg___boxed(lean_object* v_ext_243_, lean_object* v_b_244_, lean_object* v_kind_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_kind_boxed_249_; lean_object* v_res_250_; 
v_kind_boxed_249_ = lean_unbox(v_kind_245_);
v_res_250_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_243_, v_b_244_, v_kind_boxed_249_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_00_u03c3_253_, lean_object* v_ext_254_, lean_object* v_b_255_, uint8_t v_kind_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_254_, v_b_255_, v_kind_256_, v___y_257_, v___y_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_00_u03c3_263_, lean_object* v_ext_264_, lean_object* v_b_265_, lean_object* v_kind_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
uint8_t v_kind_boxed_270_; lean_object* v_res_271_; 
v_kind_boxed_270_ = lean_unbox(v_kind_266_);
v_res_271_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0(v_00_u03b1_261_, v_00_u03b2_262_, v_00_u03c3_263_, v_ext_264_, v_b_265_, v_kind_boxed_270_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr(lean_object* v_declName_275_, uint8_t v_kind_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___closed__1));
lean_inc(v_declName_275_);
v___x_281_ = l_Lean_ensureAttrDeclIsMeta(v___x_280_, v_declName_275_, v_kind_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_309_; 
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; 
v_unused_310_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_310_);
v___x_283_ = v___x_281_;
v_isShared_284_ = v_isSharedCheck_309_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___x_281_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_309_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v_env_286_; lean_object* v_options_287_; lean_object* v_ref_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_285_ = lean_st_ref_get(v_a_278_);
v_env_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref(v_env_286_);
lean_dec(v___x_285_);
v_options_287_ = lean_ctor_get(v_a_277_, 2);
v_ref_288_ = lean_ctor_get(v_a_277_, 5);
lean_inc_ref(v_options_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_env_286_);
lean_ctor_set(v___x_289_, 1, v_options_287_);
lean_inc(v_declName_275_);
v___x_290_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_getFrameProcFromDeclImpl(v_declName_275_, v___x_289_);
lean_dec_ref_known(v___x_289_, 2);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_del_object(v___x_283_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_frameProcExt;
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_declName_275_);
lean_ctor_set(v___x_293_, 1, v_a_291_);
v___x_294_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr_spec__0___redArg(v___x_292_, v___x_293_, v_kind_276_, v_a_277_, v_a_278_);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_308_; 
lean_dec(v_declName_275_);
v_a_295_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_308_ == 0)
{
v___x_297_ = v___x_290_;
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_290_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_io_error_to_string(v_a_295_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 3);
lean_ctor_set(v___x_283_, 0, v___x_299_);
v___x_301_ = v___x_283_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_307_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
lean_inc(v_ref_288_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v_ref_288_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_303_);
v___x_305_ = v___x_297_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_275_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr___boxed(lean_object* v_declName_311_, lean_object* v_kind_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_kind_boxed_316_; lean_object* v_res_317_; 
v_kind_boxed_316_ = lean_unbox(v_kind_312_);
v_res_317_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr(v_declName_311_, v_kind_boxed_316_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v_declName_318_, lean_object* v___stx_319_, uint8_t v_kind_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_addFrameProcAttr(v_declName_318_, v_kind_320_, v___y_321_, v___y_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_declName_325_, lean_object* v___stx_326_, lean_object* v_kind_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v_kind_boxed_331_; lean_object* v_res_332_; 
v_kind_boxed_331_ = lean_unbox(v_kind_327_);
v_res_332_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v_declName_325_, v___stx_326_, v_kind_boxed_331_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___stx_326_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_333_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_336_);
lean_ctor_set(v___x_338_, 5, v___x_336_);
lean_ctor_set(v___x_338_, 6, v___x_336_);
lean_ctor_set(v___x_338_, 7, v___x_336_);
lean_ctor_set(v___x_338_, 8, v___x_336_);
lean_ctor_set(v___x_338_, 9, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_unsigned_to_nat(32u);
v___x_340_ = lean_mk_empty_array_with_capacity(v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_342_ = ((size_t)5ULL);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_unsigned_to_nat(32u);
v___x_345_ = lean_mk_empty_array_with_capacity(v___x_344_);
v___x_346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_347_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
lean_ctor_set(v___x_347_, 2, v___x_343_);
lean_ctor_set(v___x_347_, 3, v___x_343_);
lean_ctor_set_usize(v___x_347_, 4, v___x_342_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = lean_box(1);
v___x_349_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_350_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_349_);
lean_ctor_set(v___x_351_, 2, v___x_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_env_357_; lean_object* v_options_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_356_ = lean_st_ref_get(v___y_354_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_356_);
v_options_358_ = lean_ctor_get(v___y_353_, 2);
v___x_359_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_360_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_358_);
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v_env_357_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
lean_ctor_set(v___x_361_, 2, v___x_360_);
lean_ctor_set(v___x_361_, 3, v_options_358_);
v___x_362_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_msgData_352_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msgData_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_ref_373_; lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_383_; 
v_ref_373_ = lean_ctor_get(v___y_370_, 5);
v___x_374_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msg_369_, v___y_370_, v___y_371_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_383_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_383_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_inc(v_ref_373_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_ref_373_);
lean_ctor_set(v___x_379_, 1, v_a_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 1);
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_388_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v___x_395_, lean_object* v_decl_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_400_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_401_ = l_Lean_MessageData_ofName(v___x_395_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v___x_404_, v___y_397_, v___y_398_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v___x_406_, lean_object* v_decl_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v___x_406_, v_decl_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v_decl_407_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_517_ = l_Lean_registerBuiltinAttribute(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(v_00_u03b1_526_, v_msg_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_531_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_Internal_VCGen_frameProcExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_frameProcExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_Do_Internal_VCGen_initFn_00___x40_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcAttr(builtin);
}
#ifdef __cplusplus
}
#endif
