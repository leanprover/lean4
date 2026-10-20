// Lean compiler output
// Module: Lean.Compiler.LCNF.ExpandResetReuse
// Imports: public import Lean.Compiler.LCNF.PassManager import Init.While
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ExpandResetReuse"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.eraseProjIncFor"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "assertion violation: n > 0 -- 0 incs should not be happening\n      "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.remapSets"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.partitionSelfSets"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unused"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 23, 1, 196, 228, 87, 228, 117)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "reuseFailAlloc"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 58, 180, 100, 190, 122, 70, 27)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reusejp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 245, 4, 252, 178, 144, 44, 230)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "assertion violation: n == 1 -- n must be one since `resetToken := reset ...`\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.processResetCont"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isShared"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 21, 27, 150, 131, 176, 68, 226)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "resetjp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 44, 28, 106, 212, 154, 129, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isSharedCheck"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 46, 40, 117, 142, 84, 34, 112)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandResetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 183, 62, 154, 7, 128, 85, 195)}};
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_expandResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_expandResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_expandResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 164, 249, 156, 95, 195, 57, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ExpandResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 11, 111, 203, 109, 196, 117, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(154, 243, 191, 84, 138, 53, 176, 74)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 105, 247, 180, 77, 138, 39, 85)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 100, 40, 107, 220, 34, 211, 1)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 232, 133, 20, 223, 27, 247, 220)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 148, 15, 20, 202, 87, 70, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 233, 102, 190, 62, 169, 58, 201)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 94, 182, 88, 148, 161, 255, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 201, 67, 31, 121, 57, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 72, 63, 210, 236, 125, 229)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 64, 204, 59, 236, 250, 223, 228)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Array_instInhabited___redArg();
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(lean_object* v_msg_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v_toApplicative_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_49_; 
v___x_11_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_12_ = l_StateRefT_x27_instMonad___redArg(v___x_11_);
v_toApplicative_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v___x_12_, 1);
lean_dec(v_unused_50_);
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_49_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_toApplicative_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_49_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_toFunctor_17_; lean_object* v_toSeq_18_; lean_object* v_toSeqLeft_19_; lean_object* v_toSeqRight_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_47_; 
v_toFunctor_17_ = lean_ctor_get(v_toApplicative_13_, 0);
v_toSeq_18_ = lean_ctor_get(v_toApplicative_13_, 2);
v_toSeqLeft_19_ = lean_ctor_get(v_toApplicative_13_, 3);
v_toSeqRight_20_ = lean_ctor_get(v_toApplicative_13_, 4);
v_isSharedCheck_47_ = !lean_is_exclusive(v_toApplicative_13_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v_toApplicative_13_, 1);
lean_dec(v_unused_48_);
v___x_22_ = v_toApplicative_13_;
v_isShared_23_ = v_isSharedCheck_47_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_toSeqRight_20_);
lean_inc(v_toSeqLeft_19_);
lean_inc(v_toSeq_18_);
lean_inc(v_toFunctor_17_);
lean_dec(v_toApplicative_13_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_47_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___f_31_; lean_object* v___x_33_; 
v___f_24_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_25_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_17_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_26_, 0, v_toFunctor_17_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_27_, 0, v_toFunctor_17_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___f_26_);
lean_ctor_set(v___x_28_, 1, v___f_27_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_29_, 0, v_toSeqRight_20_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_30_, 0, v_toSeqLeft_19_);
v___f_31_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_31_, 0, v_toSeq_18_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 4, v___f_29_);
lean_ctor_set(v___x_22_, 3, v___f_30_);
lean_ctor_set(v___x_22_, 2, v___f_31_);
lean_ctor_set(v___x_22_, 1, v___f_24_);
lean_ctor_set(v___x_22_, 0, v___x_28_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___f_24_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v___f_31_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v___f_30_);
lean_ctor_set(v_reuseFailAlloc_46_, 4, v___f_29_);
v___x_33_ = v_reuseFailAlloc_46_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_35_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___f_25_);
lean_ctor_set(v___x_15_, 0, v___x_33_);
v___x_35_ = v___x_15_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___f_25_);
v___x_35_ = v_reuseFailAlloc_45_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_2621__overap_43_; lean_object* v___x_44_; 
v___x_36_ = l_StateRefT_x27_instMonad___redArg(v___x_35_);
v___x_37_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_37_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
v___x_41_ = l_instInhabitedOfMonad___redArg(v___x_36_, v___x_40_);
v___f_42_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_42_, 0, v___x_41_);
v___x_2621__overap_43_ = lean_panic_fn_borrowed(v___f_42_, v_msg_5_);
lean_dec_ref(v___f_42_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
v___x_44_ = lean_apply_5(v___x_2621__overap_43_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object* v_fst_58_, lean_object* v_snd_59_, lean_object* v_fst_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_fst_58_);
lean_ctor_set(v___x_67_, 1, v_snd_59_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v_fst_60_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object* v_fst_71_, lean_object* v_snd_72_, lean_object* v_fst_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_71_, v_snd_72_, v_fst_73_, v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec_ref(v_x_74_);
return v_res_80_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_81_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3));
v___x_86_ = lean_unsigned_to_nat(6u);
v___x_87_ = lean_unsigned_to_nat(87u);
v___x_88_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2));
v___x_89_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_90_ = l_mkPanicMessageWithDecl(v___x_89_, v___x_88_, v___x_87_, v___x_86_, v___x_85_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object* v_targetId_91_, lean_object* v_a_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___y_99_; lean_object* v_snd_119_; lean_object* v_fst_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_266_; 
v_snd_119_ = lean_ctor_get(v_a_92_, 1);
v_fst_120_ = lean_ctor_get(v_a_92_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_92_);
if (v_isSharedCheck_266_ == 0)
{
v___x_122_ = v_a_92_;
v_isShared_123_ = v_isSharedCheck_266_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_119_);
lean_inc(v_fst_120_);
lean_dec(v_a_92_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_266_;
goto v_resetjp_121_;
}
v___jp_98_:
{
if (lean_obj_tag(v___y_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_110_; 
v_a_100_ = lean_ctor_get(v___y_99_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___y_99_);
if (v_isSharedCheck_110_ == 0)
{
v___x_102_ = v___y_99_;
v_isShared_103_ = v_isSharedCheck_110_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___y_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_110_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
if (lean_obj_tag(v_a_100_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; 
v_a_104_ = lean_ctor_get(v_a_100_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v_a_100_, 1);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_a_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
else
{
lean_object* v_a_108_; 
lean_del_object(v___x_102_);
v_a_108_ = lean_ctor_get(v_a_100_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v_a_100_, 1);
v_a_92_ = v_a_108_;
goto _start;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___y_99_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___y_99_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___y_99_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___y_99_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
v_resetjp_121_:
{
lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_265_; 
v_fst_124_ = lean_ctor_get(v_snd_119_, 0);
v_snd_125_ = lean_ctor_get(v_snd_119_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_snd_119_);
if (v_isSharedCheck_265_ == 0)
{
v___x_127_ = v_snd_119_;
v_isShared_128_ = v_isSharedCheck_265_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snd_125_);
lean_inc(v_fst_124_);
lean_dec(v_snd_119_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_265_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_array_get_size(v_fst_120_);
v___x_139_ = lean_nat_dec_le(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_del_object(v___x_127_);
lean_del_object(v___x_122_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_fst_124_);
lean_ctor_set(v___x_140_, 1, v_snd_125_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v_fst_120_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_sub(v___x_138_, v___x_144_);
v___x_146_ = lean_array_get(v___x_143_, v_fst_120_, v___x_145_);
lean_dec(v___x_145_);
switch(lean_obj_tag(v___x_146_))
{
case 0:
{
lean_object* v_decl_147_; lean_object* v_value_148_; 
lean_del_object(v___x_127_);
lean_del_object(v___x_122_);
v_decl_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc_ref(v_decl_147_);
v_value_148_ = lean_ctor_get(v_decl_147_, 3);
lean_inc(v_value_148_);
switch(lean_obj_tag(v_value_148_))
{
case 8:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec_ref_known(v_value_148_, 3);
lean_dec_ref(v_decl_147_);
v___x_149_ = lean_array_pop(v_fst_120_);
v___x_150_ = lean_array_push(v_fst_124_, v___x_146_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_snd_125_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_149_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v_a_92_ = v___x_152_;
goto _start;
}
case 7:
{
lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v_decl_147_);
v_isSharedCheck_164_ = !lean_is_exclusive(v_value_148_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; lean_object* v_unused_166_; 
v_unused_165_ = lean_ctor_get(v_value_148_, 1);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_value_148_, 0);
lean_dec(v_unused_166_);
v___x_155_ = v_value_148_;
v_isShared_156_ = v_isSharedCheck_164_;
goto v_resetjp_154_;
}
else
{
lean_dec(v_value_148_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_164_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_157_ = lean_array_pop(v_fst_120_);
v___x_158_ = lean_array_push(v_fst_124_, v___x_146_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 0);
lean_ctor_set(v___x_155_, 1, v_snd_125_);
lean_ctor_set(v___x_155_, 0, v___x_158_);
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_snd_125_);
v___x_160_ = v_reuseFailAlloc_163_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v_a_92_ = v___x_161_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_185_; 
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_146_, 0);
lean_dec(v_unused_186_);
v___x_168_ = v___x_146_;
v_isShared_169_ = v_isSharedCheck_185_;
goto v_resetjp_167_;
}
else
{
lean_dec(v___x_146_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_185_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_fvarId_170_; lean_object* v_binderName_171_; lean_object* v_type_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_183_; 
v_fvarId_170_ = lean_ctor_get(v_decl_147_, 0);
v_binderName_171_ = lean_ctor_get(v_decl_147_, 1);
v_type_172_ = lean_ctor_get(v_decl_147_, 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v_decl_147_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_decl_147_, 3);
lean_dec(v_unused_184_);
v___x_174_ = v_decl_147_;
v_isShared_175_ = v_isSharedCheck_183_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_type_172_);
lean_inc(v_binderName_171_);
lean_inc(v_fvarId_170_);
lean_dec(v_decl_147_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_183_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fvarId_170_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_binderName_171_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_type_172_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_value_148_);
v___x_177_ = v_reuseFailAlloc_182_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_177_);
v___x_179_ = v___x_168_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_124_, v_snd_125_, v_fst_120_, v___x_179_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___x_179_);
v___y_99_ = v___x_180_;
goto v___jp_98_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_187_; lean_object* v_n_188_; uint8_t v_check_189_; uint8_t v_persistent_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_fvarId_187_ = lean_ctor_get(v___x_146_, 0);
v_n_188_ = lean_ctor_get(v___x_146_, 1);
v_check_189_ = lean_ctor_get_uint8(v___x_146_, sizeof(void*)*2);
v_persistent_190_ = lean_ctor_get_uint8(v___x_146_, sizeof(void*)*2 + 1);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_nat_dec_lt(v___x_191_, v_n_188_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref_known(v___x_146_, 2);
lean_del_object(v___x_127_);
lean_dec(v_snd_125_);
lean_dec(v_fst_124_);
lean_del_object(v___x_122_);
lean_dec(v_fst_120_);
v___x_193_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
v___x_194_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_193_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
v___y_99_ = v___x_194_;
goto v___jp_98_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_nat_sub(v___x_138_, v___x_137_);
v___x_196_ = lean_array_get(v___x_143_, v_fst_120_, v___x_195_);
lean_dec(v___x_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_decl_197_; lean_object* v_value_198_; 
v_decl_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_decl_197_);
v_value_198_ = lean_ctor_get(v_decl_197_, 3);
lean_inc(v_value_198_);
if (lean_obj_tag(v_value_198_) == 6)
{
lean_object* v_fvarId_199_; lean_object* v_i_200_; lean_object* v_var_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_242_; 
v_fvarId_199_ = lean_ctor_get(v_decl_197_, 0);
lean_inc(v_fvarId_199_);
lean_dec_ref(v_decl_197_);
v_i_200_ = lean_ctor_get(v_value_198_, 0);
v_var_201_ = lean_ctor_get(v_value_198_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_value_198_);
if (v_isSharedCheck_242_ == 0)
{
v___x_203_ = v_value_198_;
v_isShared_204_ = v_isSharedCheck_242_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_var_201_);
lean_inc(v_i_200_);
lean_dec(v_value_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_242_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_instBEqFVarId_beq(v_fvarId_199_, v_fvarId_187_);
lean_dec(v_fvarId_199_);
if (v___x_205_ == 0)
{
lean_del_object(v___x_203_);
lean_dec(v_var_201_);
lean_dec(v_i_200_);
lean_dec_ref_known(v___x_196_, 1);
lean_dec_ref_known(v___x_146_, 2);
goto v___jp_129_;
}
else
{
uint8_t v___x_206_; 
v___x_206_ = l_Lean_instBEqFVarId_beq(v_targetId_91_, v_var_201_);
lean_dec(v_var_201_);
if (v___x_206_ == 0)
{
lean_del_object(v___x_203_);
lean_dec(v_i_200_);
lean_dec_ref_known(v___x_196_, 1);
lean_dec_ref_known(v___x_146_, 2);
goto v___jp_129_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_del_object(v___x_127_);
lean_del_object(v___x_122_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_array_get_borrowed(v___x_207_, v_snd_125_, v_i_200_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_230_; 
lean_inc(v_n_188_);
lean_inc(v_fvarId_187_);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_231_ = lean_ctor_get(v___x_146_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v___x_146_, 0);
lean_dec(v_unused_232_);
v___x_210_ = v___x_146_;
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
else
{
lean_dec(v___x_146_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___y_217_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_212_ = lean_array_pop(v_fst_120_);
v___x_213_ = lean_array_pop(v___x_212_);
lean_inc(v_fvarId_187_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_fvarId_187_);
v___x_215_ = lean_array_set(v_snd_125_, v_i_200_, v___x_214_);
lean_dec(v_i_200_);
v___x_223_ = lean_array_push(v_fst_124_, v___x_196_);
v___x_224_ = lean_nat_dec_eq(v_n_188_, v___x_144_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_nat_sub(v_n_188_, v___x_144_);
lean_dec(v_n_188_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_225_);
v___x_227_ = v___x_210_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_fvarId_187_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_225_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*2, v_check_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*2 + 1, v_persistent_190_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = lean_array_push(v___x_223_, v___x_227_);
v___y_217_ = v___x_228_;
goto v___jp_216_;
}
}
else
{
lean_del_object(v___x_210_);
lean_dec(v_n_188_);
lean_dec(v_fvarId_187_);
v___y_217_ = v___x_223_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 0);
lean_ctor_set(v___x_203_, 1, v___x_215_);
lean_ctor_set(v___x_203_, 0, v___y_217_);
v___x_219_ = v___x_203_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___y_217_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_215_);
v___x_219_ = v_reuseFailAlloc_222_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_213_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v_a_92_ = v___x_220_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
lean_dec(v_i_200_);
v___x_233_ = lean_array_push(v_fst_124_, v___x_146_);
v___x_234_ = lean_array_push(v___x_233_, v___x_196_);
v___x_235_ = lean_array_pop(v_fst_120_);
v___x_236_ = lean_array_pop(v___x_235_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 0);
lean_ctor_set(v___x_203_, 1, v_snd_125_);
lean_ctor_set(v___x_203_, 0, v___x_234_);
v___x_238_ = v___x_203_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_snd_125_);
v___x_238_ = v_reuseFailAlloc_241_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_236_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v_a_92_ = v___x_239_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref_known(v___x_146_, 2);
lean_del_object(v___x_127_);
lean_del_object(v___x_122_);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v___x_196_, 0);
lean_dec(v_unused_262_);
v___x_244_ = v___x_196_;
v_isShared_245_ = v_isSharedCheck_261_;
goto v_resetjp_243_;
}
else
{
lean_dec(v___x_196_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_261_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_fvarId_246_; lean_object* v_binderName_247_; lean_object* v_type_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_259_; 
v_fvarId_246_ = lean_ctor_get(v_decl_197_, 0);
v_binderName_247_ = lean_ctor_get(v_decl_197_, 1);
v_type_248_ = lean_ctor_get(v_decl_197_, 2);
v_isSharedCheck_259_ = !lean_is_exclusive(v_decl_197_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; 
v_unused_260_ = lean_ctor_get(v_decl_197_, 3);
lean_dec(v_unused_260_);
v___x_250_ = v_decl_197_;
v_isShared_251_ = v_isSharedCheck_259_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_type_248_);
lean_inc(v_binderName_247_);
lean_inc(v_fvarId_246_);
lean_dec(v_decl_197_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_259_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_fvarId_246_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_binderName_247_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_type_248_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_value_198_);
v___x_253_ = v_reuseFailAlloc_258_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_255_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_253_);
v___x_255_ = v___x_244_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_124_, v_snd_125_, v_fst_120_, v___x_255_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___x_255_);
v___y_99_ = v___x_256_;
goto v___jp_98_;
}
}
}
}
}
}
else
{
lean_object* v___x_263_; 
lean_dec_ref_known(v___x_146_, 2);
lean_del_object(v___x_127_);
lean_del_object(v___x_122_);
v___x_263_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_124_, v_snd_125_, v_fst_120_, v___x_196_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___x_196_);
v___y_99_ = v___x_263_;
goto v___jp_98_;
}
}
}
default: 
{
lean_object* v___x_264_; 
lean_del_object(v___x_127_);
lean_del_object(v___x_122_);
v___x_264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_124_, v_snd_125_, v_fst_120_, v___x_146_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___x_146_);
v___y_99_ = v___x_264_;
goto v___jp_98_;
}
}
}
v___jp_129_:
{
lean_object* v___x_131_; 
if (v_isShared_128_ == 0)
{
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_fst_124_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_snd_125_);
v___x_131_ = v_reuseFailAlloc_136_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_131_);
v___x_133_ = v___x_122_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_fst_120_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object* v_targetId_267_, lean_object* v_a_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_267_, v_a_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v_targetId_267_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_277_, lean_object* v_targetId_278_, lean_object* v_ds_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_keep_285_; lean_object* v___x_286_; lean_object* v_mask_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_keep_285_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_286_ = lean_box(0);
v_mask_287_ = lean_mk_array(v_nFields_277_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v_keep_285_);
lean_ctor_set(v___x_288_, 1, v_mask_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_ds_279_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_278_, v___x_289_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_311_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v_snd_295_; lean_object* v_fst_296_; lean_object* v_fst_297_; lean_object* v_snd_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_310_; 
v_snd_295_ = lean_ctor_get(v_a_291_, 1);
lean_inc(v_snd_295_);
v_fst_296_ = lean_ctor_get(v_a_291_, 0);
lean_inc(v_fst_296_);
lean_dec(v_a_291_);
v_fst_297_ = lean_ctor_get(v_snd_295_, 0);
v_snd_298_ = lean_ctor_get(v_snd_295_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_snd_295_);
if (v_isSharedCheck_310_ == 0)
{
v___x_300_ = v_snd_295_;
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_298_);
lean_inc(v_fst_297_);
lean_dec(v_snd_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = l_Array_reverse___redArg(v_fst_297_);
v___x_303_ = l_Array_append___redArg(v_fst_296_, v___x_302_);
lean_dec_ref(v___x_302_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_303_);
v___x_305_ = v___x_300_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_snd_298_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_305_);
v___x_307_ = v___x_293_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
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
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_290_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_290_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_320_, lean_object* v_targetId_321_, lean_object* v_ds_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_320_, v_targetId_321_, v_ds_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_targetId_321_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_329_, lean_object* v_inst_330_, lean_object* v_a_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_329_, v_a_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* v_targetId_338_, lean_object* v_inst_339_, lean_object* v_a_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_338_, v_inst_339_, v_a_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v_targetId_338_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_363_, lean_object* v_discrType_364_, lean_object* v_resultType_365_, lean_object* v_t_366_, lean_object* v_e_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_369_ = l_Lean_Expr_getAppFn(v_discrType_364_);
v___x_370_ = l_Lean_Expr_constName_x21(v___x_369_);
lean_dec_ref(v___x_369_);
v___x_371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_e_367_);
v___x_373_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_t_366_);
v___x_375_ = lean_unsigned_to_nat(2u);
v___x_376_ = lean_mk_empty_array_with_capacity(v___x_375_);
v___x_377_ = lean_array_push(v___x_376_, v___x_372_);
v___x_378_ = lean_array_push(v___x_377_, v___x_374_);
v___x_379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_379_, 0, v___x_370_);
lean_ctor_set(v___x_379_, 1, v_resultType_365_);
lean_ctor_set(v___x_379_, 2, v_discr_363_);
lean_ctor_set(v___x_379_, 3, v___x_378_);
v___x_380_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_382_, lean_object* v_discrType_383_, lean_object* v_resultType_384_, lean_object* v_t_385_, lean_object* v_e_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_382_, v_discrType_383_, v_resultType_384_, v_t_385_, v_e_386_);
lean_dec_ref(v_discrType_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_389_, lean_object* v_discrType_390_, lean_object* v_resultType_391_, lean_object* v_t_392_, lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_389_, v_discrType_390_, v_resultType_391_, v_t_392_, v_e_393_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_400_, lean_object* v_discrType_401_, lean_object* v_resultType_402_, lean_object* v_t_403_, lean_object* v_e_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_400_, v_discrType_401_, v_resultType_402_, v_t_403_, v_e_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec_ref(v_discrType_401_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_413_ = lean_panic_fn_borrowed(v___x_412_, v_msg_411_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_417_ = lean_unsigned_to_nat(11u);
v___x_418_ = lean_unsigned_to_nat(138u);
v___x_419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_420_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_421_ = l_mkPanicMessageWithDecl(v___x_420_, v___x_419_, v___x_418_, v___x_417_, v___x_416_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_422_, size_t v_sz_423_, size_t v_i_424_, lean_object* v_bs_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_lt(v_i_424_, v_sz_423_);
if (v___x_426_ == 0)
{
lean_dec(v_targetId_422_);
return v_bs_425_;
}
else
{
lean_object* v_v_427_; lean_object* v___x_428_; lean_object* v_bs_x27_429_; lean_object* v___y_431_; 
v_v_427_ = lean_array_uget(v_bs_425_, v_i_424_);
v___x_428_ = lean_unsigned_to_nat(0u);
v_bs_x27_429_ = lean_array_uset(v_bs_425_, v_i_424_, v___x_428_);
switch(lean_obj_tag(v_v_427_))
{
case 3:
{
lean_object* v_i_436_; lean_object* v_y_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_i_436_ = lean_ctor_get(v_v_427_, 1);
v_y_437_ = lean_ctor_get(v_v_427_, 2);
v_isSharedCheck_444_ = !lean_is_exclusive(v_v_427_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v_v_427_, 0);
lean_dec(v_unused_445_);
v___x_439_ = v_v_427_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_y_437_);
lean_inc(v_i_436_);
lean_dec(v_v_427_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
lean_inc(v_targetId_422_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_targetId_422_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_targetId_422_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_i_436_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_y_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v___y_431_ = v___x_442_;
goto v___jp_430_;
}
}
}
case 5:
{
lean_object* v_i_446_; lean_object* v_offset_447_; lean_object* v_y_448_; lean_object* v_ty_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_i_446_ = lean_ctor_get(v_v_427_, 1);
v_offset_447_ = lean_ctor_get(v_v_427_, 2);
v_y_448_ = lean_ctor_get(v_v_427_, 3);
v_ty_449_ = lean_ctor_get(v_v_427_, 4);
v_isSharedCheck_456_ = !lean_is_exclusive(v_v_427_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_v_427_, 0);
lean_dec(v_unused_457_);
v___x_451_ = v_v_427_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_ty_449_);
lean_inc(v_y_448_);
lean_inc(v_offset_447_);
lean_inc(v_i_446_);
lean_dec(v_v_427_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
lean_inc(v_targetId_422_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_targetId_422_);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_targetId_422_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_i_446_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_offset_447_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_y_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_ty_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
v___y_431_ = v___x_454_;
goto v___jp_430_;
}
}
}
case 4:
{
lean_object* v_i_458_; lean_object* v_y_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_i_458_ = lean_ctor_get(v_v_427_, 1);
v_y_459_ = lean_ctor_get(v_v_427_, 2);
v_isSharedCheck_466_ = !lean_is_exclusive(v_v_427_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_v_427_, 0);
lean_dec(v_unused_467_);
v___x_461_ = v_v_427_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_y_459_);
lean_inc(v_i_458_);
lean_dec(v_v_427_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
lean_inc(v_targetId_422_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v_targetId_422_);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_targetId_422_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_i_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_y_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v___y_431_ = v___x_464_;
goto v___jp_430_;
}
}
}
default: 
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_v_427_);
v___x_468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_469_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_468_);
v___y_431_ = v___x_469_;
goto v___jp_430_;
}
}
v___jp_430_:
{
size_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_424_, v___x_432_);
v___x_434_ = lean_array_uset(v_bs_x27_429_, v_i_424_, v___y_431_);
v_i_424_ = v___x_433_;
v_bs_425_ = v___x_434_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_470_, lean_object* v_sz_471_, lean_object* v_i_472_, lean_object* v_bs_473_){
_start:
{
size_t v_sz_boxed_474_; size_t v_i_boxed_475_; lean_object* v_res_476_; 
v_sz_boxed_474_ = lean_unbox_usize(v_sz_471_);
lean_dec(v_sz_471_);
v_i_boxed_475_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_470_, v_sz_boxed_474_, v_i_boxed_475_, v_bs_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_477_, lean_object* v_sets_478_){
_start:
{
size_t v_sz_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_sz_480_ = lean_array_size(v_sets_478_);
v___x_481_ = ((size_t)0ULL);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_477_, v_sz_480_, v___x_481_, v_sets_478_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_484_, lean_object* v_sets_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_484_, v_sets_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_488_, lean_object* v_sets_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_488_, v_sets_489_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_496_, lean_object* v_sets_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_496_, v_sets_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_504_, lean_object* v_i_505_, lean_object* v_y_506_, lean_object* v_a_507_){
_start:
{
if (lean_obj_tag(v_y_506_) == 0)
{
uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = 0;
v___x_510_ = lean_box(v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_fvarId_512_; uint8_t v___x_513_; lean_object* v___x_514_; 
v_fvarId_512_ = lean_ctor_get(v_y_506_, 0);
v___x_513_ = 1;
v___x_514_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_513_, v_fvarId_512_, v_a_507_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_542_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_542_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_542_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_542_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
if (lean_obj_tag(v_a_515_) == 1)
{
lean_object* v_val_519_; 
v_val_519_ = lean_ctor_get(v_a_515_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_a_515_, 1);
if (lean_obj_tag(v_val_519_) == 6)
{
lean_object* v_i_520_; lean_object* v_var_521_; uint8_t v___x_522_; 
v_i_520_ = lean_ctor_get(v_val_519_, 0);
lean_inc(v_i_520_);
v_var_521_ = lean_ctor_get(v_val_519_, 1);
lean_inc(v_var_521_);
lean_dec_ref_known(v_val_519_, 2);
v___x_522_ = lean_nat_dec_eq(v_i_505_, v_i_520_);
lean_dec(v_i_520_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec(v_var_521_);
v___x_523_ = lean_box(v___x_522_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_523_);
v___x_525_ = v___x_517_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = l_Lean_instBEqFVarId_beq(v_fvarId_504_, v_var_521_);
lean_dec(v_var_521_);
v___x_528_ = lean_box(v___x_527_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_528_);
v___x_530_ = v___x_517_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
lean_dec(v_val_519_);
v___x_532_ = 0;
v___x_533_ = lean_box(v___x_532_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_533_);
v___x_535_ = v___x_517_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
lean_dec(v_a_515_);
v___x_537_ = 0;
v___x_538_ = lean_box(v___x_537_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_538_);
v___x_540_ = v___x_517_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_543_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_514_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_514_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_551_, lean_object* v_i_552_, lean_object* v_y_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_551_, v_i_552_, v_y_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec(v_y_553_);
lean_dec(v_i_552_);
lean_dec(v_fvarId_551_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_557_, lean_object* v_i_558_, lean_object* v_y_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_557_, v_i_558_, v_y_559_, v_a_561_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_566_, lean_object* v_i_567_, lean_object* v_y_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_566_, v_i_567_, v_y_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_y_568_);
lean_dec(v_i_567_);
lean_dec(v_fvarId_566_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_575_, lean_object* v_i_576_, lean_object* v_y_577_, lean_object* v_a_578_){
_start:
{
uint8_t v___x_580_; lean_object* v___x_581_; 
v___x_580_ = 1;
v___x_581_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_580_, v_y_577_, v_a_578_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_609_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_609_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_609_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_609_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
if (lean_obj_tag(v_a_582_) == 1)
{
lean_object* v_val_586_; 
v_val_586_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v_a_582_, 1);
if (lean_obj_tag(v_val_586_) == 7)
{
lean_object* v_i_587_; lean_object* v_var_588_; uint8_t v___x_589_; 
v_i_587_ = lean_ctor_get(v_val_586_, 0);
lean_inc(v_i_587_);
v_var_588_ = lean_ctor_get(v_val_586_, 1);
lean_inc(v_var_588_);
lean_dec_ref_known(v_val_586_, 2);
v___x_589_ = lean_nat_dec_eq(v_i_576_, v_i_587_);
lean_dec(v_i_587_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec(v_var_588_);
v___x_590_ = lean_box(v___x_589_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_590_);
v___x_592_ = v___x_584_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
else
{
uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_594_ = l_Lean_instBEqFVarId_beq(v_fvarId_575_, v_var_588_);
lean_dec(v_var_588_);
v___x_595_ = lean_box(v___x_594_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_595_);
v___x_597_ = v___x_584_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec(v_val_586_);
v___x_599_ = 0;
v___x_600_ = lean_box(v___x_599_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_600_);
v___x_602_ = v___x_584_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_a_582_);
v___x_604_ = 0;
v___x_605_ = lean_box(v___x_604_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_605_);
v___x_607_ = v___x_584_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_a_610_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_581_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_581_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_618_, lean_object* v_i_619_, lean_object* v_y_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_618_, v_i_619_, v_y_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec(v_y_620_);
lean_dec(v_i_619_);
lean_dec(v_fvarId_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_624_, lean_object* v_i_625_, lean_object* v_y_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_624_, v_i_625_, v_y_626_, v_a_628_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_633_, lean_object* v_i_634_, lean_object* v_y_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_633_, v_i_634_, v_y_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_y_635_);
lean_dec(v_i_634_);
lean_dec(v_fvarId_633_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_642_, lean_object* v_i_643_, lean_object* v_offset_644_, lean_object* v_y_645_, lean_object* v_a_646_){
_start:
{
uint8_t v___x_648_; lean_object* v___x_649_; 
v___x_648_ = 1;
v___x_649_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_648_, v_y_645_, v_a_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_683_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_683_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_683_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_683_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
if (lean_obj_tag(v_a_650_) == 1)
{
lean_object* v_val_654_; 
v_val_654_ = lean_ctor_get(v_a_650_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_a_650_, 1);
if (lean_obj_tag(v_val_654_) == 8)
{
lean_object* v_n_655_; lean_object* v_offset_656_; lean_object* v_var_657_; uint8_t v___x_658_; 
v_n_655_ = lean_ctor_get(v_val_654_, 0);
lean_inc(v_n_655_);
v_offset_656_ = lean_ctor_get(v_val_654_, 1);
lean_inc(v_offset_656_);
v_var_657_ = lean_ctor_get(v_val_654_, 2);
lean_inc(v_var_657_);
lean_dec_ref_known(v_val_654_, 3);
v___x_658_ = lean_nat_dec_eq(v_i_643_, v_n_655_);
lean_dec(v_n_655_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec(v_var_657_);
lean_dec(v_offset_656_);
v___x_659_ = lean_box(v___x_658_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_659_);
v___x_661_ = v___x_652_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_eq(v_offset_644_, v_offset_656_);
lean_dec(v_offset_656_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_dec(v_var_657_);
v___x_664_ = lean_box(v___x_663_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_664_);
v___x_666_ = v___x_652_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
else
{
uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_668_ = l_Lean_instBEqFVarId_beq(v_fvarId_642_, v_var_657_);
lean_dec(v_var_657_);
v___x_669_ = lean_box(v___x_668_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_669_);
v___x_671_ = v___x_652_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
lean_dec(v_val_654_);
v___x_673_ = 0;
v___x_674_ = lean_box(v___x_673_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_674_);
v___x_676_ = v___x_652_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_dec(v_a_650_);
v___x_678_ = 0;
v___x_679_ = lean_box(v___x_678_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_679_);
v___x_681_ = v___x_652_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
v_a_684_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_649_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_649_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_692_, lean_object* v_i_693_, lean_object* v_offset_694_, lean_object* v_y_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_692_, v_i_693_, v_offset_694_, v_y_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec(v_y_695_);
lean_dec(v_offset_694_);
lean_dec(v_i_693_);
lean_dec(v_fvarId_692_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_699_, lean_object* v_i_700_, lean_object* v_offset_701_, lean_object* v_y_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_699_, v_i_700_, v_offset_701_, v_y_702_, v_a_704_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_709_, lean_object* v_i_710_, lean_object* v_offset_711_, lean_object* v_y_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_709_, v_i_710_, v_offset_711_, v_y_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_y_712_);
lean_dec(v_offset_711_);
lean_dec(v_i_710_);
lean_dec(v_fvarId_709_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_toApplicative_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_761_; 
v___x_725_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_726_ = l_StateRefT_x27_instMonad___redArg(v___x_725_);
v_toApplicative_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_726_, 1);
lean_dec(v_unused_762_);
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_toApplicative_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_toFunctor_731_; lean_object* v_toSeq_732_; lean_object* v_toSeqLeft_733_; lean_object* v_toSeqRight_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_759_; 
v_toFunctor_731_ = lean_ctor_get(v_toApplicative_727_, 0);
v_toSeq_732_ = lean_ctor_get(v_toApplicative_727_, 2);
v_toSeqLeft_733_ = lean_ctor_get(v_toApplicative_727_, 3);
v_toSeqRight_734_ = lean_ctor_get(v_toApplicative_727_, 4);
v_isSharedCheck_759_ = !lean_is_exclusive(v_toApplicative_727_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_toApplicative_727_, 1);
lean_dec(v_unused_760_);
v___x_736_ = v_toApplicative_727_;
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_toSeqRight_734_);
lean_inc(v_toSeqLeft_733_);
lean_inc(v_toSeq_732_);
lean_inc(v_toFunctor_731_);
lean_dec(v_toApplicative_727_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_759_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_747_; 
v___f_738_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_739_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_731_);
v___f_740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_740_, 0, v_toFunctor_731_);
v___f_741_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_741_, 0, v_toFunctor_731_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___f_740_);
lean_ctor_set(v___x_742_, 1, v___f_741_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_743_, 0, v_toSeqRight_734_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_744_, 0, v_toSeqLeft_733_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_745_, 0, v_toSeq_732_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v___f_743_);
lean_ctor_set(v___x_736_, 3, v___f_744_);
lean_ctor_set(v___x_736_, 2, v___f_745_);
lean_ctor_set(v___x_736_, 1, v___f_738_);
lean_ctor_set(v___x_736_, 0, v___x_742_);
v___x_747_ = v___x_736_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___f_738_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v___f_745_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v___f_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v___f_743_);
v___x_747_ = v_reuseFailAlloc_758_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___f_739_);
lean_ctor_set(v___x_729_, 0, v___x_747_);
v___x_749_ = v___x_729_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___f_739_);
v___x_749_ = v_reuseFailAlloc_757_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_883__overap_755_; lean_object* v___x_756_; 
v___x_750_ = l_StateRefT_x27_instMonad___redArg(v___x_749_);
v___x_751_ = 0;
v___x_752_ = lean_box(v___x_751_);
v___x_753_ = l_instInhabitedOfMonad___redArg(v___x_750_, v___x_752_);
v___f_754_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_754_, 0, v___x_753_);
v___x_883__overap_755_ = lean_panic_fn_borrowed(v___f_754_, v_msg_719_);
lean_dec_ref(v___f_754_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_756_ = lean_apply_5(v___x_883__overap_755_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, lean_box(0));
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_772_ = lean_unsigned_to_nat(13u);
v___x_773_ = lean_unsigned_to_nat(174u);
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_775_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_776_ = l_mkPanicMessageWithDecl(v___x_775_, v___x_774_, v___x_773_, v___x_772_, v___x_771_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_777_, lean_object* v_as_778_, size_t v_sz_779_, size_t v_i_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_a_788_; uint8_t v___x_792_; 
v___x_792_ = lean_usize_dec_lt(v_i_780_, v_sz_779_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_b_781_);
return v___x_793_;
}
else
{
lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_832_; 
v_fst_794_ = lean_ctor_get(v_b_781_, 0);
v_snd_795_ = lean_ctor_get(v_b_781_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_b_781_);
if (v_isSharedCheck_832_ == 0)
{
v___x_797_ = v_b_781_;
v_isShared_798_ = v_isSharedCheck_832_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_inc(v_fst_794_);
lean_dec(v_b_781_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_832_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_a_799_; lean_object* v___y_801_; 
v_a_799_ = lean_array_uget_borrowed(v_as_778_, v_i_780_);
switch(lean_obj_tag(v_a_799_))
{
case 3:
{
lean_object* v_i_820_; lean_object* v_y_821_; lean_object* v___x_822_; 
v_i_820_ = lean_ctor_get(v_a_799_, 1);
v_y_821_ = lean_ctor_get(v_a_799_, 2);
v___x_822_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_777_, v_i_820_, v_y_821_, v___y_783_);
v___y_801_ = v___x_822_;
goto v___jp_800_;
}
case 4:
{
lean_object* v_i_823_; lean_object* v_y_824_; lean_object* v___x_825_; 
v_i_823_ = lean_ctor_get(v_a_799_, 1);
v_y_824_ = lean_ctor_get(v_a_799_, 2);
v___x_825_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_777_, v_i_823_, v_y_824_, v___y_783_);
v___y_801_ = v___x_825_;
goto v___jp_800_;
}
case 5:
{
lean_object* v_i_826_; lean_object* v_offset_827_; lean_object* v_y_828_; lean_object* v___x_829_; 
v_i_826_ = lean_ctor_get(v_a_799_, 1);
v_offset_827_ = lean_ctor_get(v_a_799_, 2);
v_y_828_ = lean_ctor_get(v_a_799_, 3);
v___x_829_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_777_, v_i_826_, v_offset_827_, v_y_828_, v___y_783_);
v___y_801_ = v___x_829_;
goto v___jp_800_;
}
default: 
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_831_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_830_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
v___y_801_ = v___x_831_;
goto v___jp_800_;
}
}
v___jp_800_:
{
if (lean_obj_tag(v___y_801_) == 0)
{
lean_object* v_a_802_; uint8_t v___x_803_; 
v_a_802_ = lean_ctor_get(v___y_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___y_801_, 1);
v___x_803_ = lean_unbox(v_a_802_);
lean_dec(v_a_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_a_799_);
v___x_804_ = lean_array_push(v_fst_794_, v_a_799_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_795_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v_a_788_ = v___x_806_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_inc(v_a_799_);
v___x_808_ = lean_array_push(v_snd_795_, v_a_799_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_808_);
v___x_810_ = v___x_797_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_fst_794_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
v_a_788_ = v___x_810_;
goto v___jp_787_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
v_a_812_ = lean_ctor_get(v___y_801_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___y_801_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___y_801_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___y_801_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
v___jp_787_:
{
size_t v___x_789_; size_t v___x_790_; 
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_add(v_i_780_, v___x_789_);
v_i_780_ = v___x_790_;
v_b_781_ = v_a_788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_833_, lean_object* v_as_834_, lean_object* v_sz_835_, lean_object* v_i_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
size_t v_sz_boxed_843_; size_t v_i_boxed_844_; lean_object* v_res_845_; 
v_sz_boxed_843_ = lean_unbox_usize(v_sz_835_);
lean_dec(v_sz_835_);
v_i_boxed_844_ = lean_unbox_usize(v_i_836_);
lean_dec(v_i_836_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_833_, v_as_834_, v_sz_boxed_843_, v_i_boxed_844_, v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v_as_834_);
lean_dec(v_selfId_833_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_848_, lean_object* v_sets_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_856_ = lean_array_size(v_sets_849_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_848_, v_sets_849_, v_sz_856_, v___x_857_, v___x_855_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_875_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_875_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_875_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_875_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_fst_863_ = lean_ctor_get(v_a_859_, 0);
v_snd_864_ = lean_ctor_get(v_a_859_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_874_ == 0)
{
v___x_866_ = v_a_859_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snd_864_);
lean_inc(v_fst_863_);
lean_dec(v_a_859_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_fst_863_);
lean_ctor_set(v___x_866_, 0, v_snd_864_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_snd_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_fst_863_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_869_);
v___x_871_ = v___x_861_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
else
{
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_876_, lean_object* v_sets_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_876_, v_sets_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec_ref(v_sets_877_);
lean_dec(v_selfId_876_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_snd_887_; 
v_snd_887_ = lean_ctor_get(v_a_885_, 1);
lean_inc(v_snd_887_);
switch(lean_obj_tag(v_snd_887_))
{
case 7:
{
lean_object* v_fst_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_906_; 
v_fst_888_ = lean_ctor_get(v_a_885_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_a_885_, 1);
lean_dec(v_unused_907_);
v___x_890_ = v_a_885_;
v_isShared_891_ = v_isSharedCheck_906_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_fst_888_);
lean_dec(v_a_885_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_906_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_fvarId_892_; lean_object* v_k_893_; uint8_t v___x_894_; 
v_fvarId_892_ = lean_ctor_get(v_snd_887_, 0);
v_k_893_ = lean_ctor_get(v_snd_887_, 3);
v___x_894_ = l_Lean_instBEqFVarId_beq(v_target_884_, v_fvarId_892_);
if (v___x_894_ == 0)
{
lean_object* v___x_896_; 
if (v_isShared_891_ == 0)
{
v___x_896_ = v___x_890_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_888_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_snd_887_);
v___x_896_ = v_reuseFailAlloc_898_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
else
{
uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
lean_inc_ref(v_k_893_);
v___x_899_ = 1;
v___x_900_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_899_, v_snd_887_);
lean_dec_ref_known(v_snd_887_, 4);
v___x_901_ = lean_array_push(v_fst_888_, v___x_900_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_k_893_);
lean_ctor_set(v___x_890_, 0, v___x_901_);
v___x_903_ = v___x_890_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_893_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
v_a_885_ = v___x_903_;
goto _start;
}
}
}
}
case 9:
{
lean_object* v_fst_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_926_; 
v_fst_908_ = lean_ctor_get(v_a_885_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_a_885_, 1);
lean_dec(v_unused_927_);
v___x_910_ = v_a_885_;
v_isShared_911_ = v_isSharedCheck_926_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_fst_908_);
lean_dec(v_a_885_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_926_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_fvarId_912_; lean_object* v_k_913_; uint8_t v___x_914_; 
v_fvarId_912_ = lean_ctor_get(v_snd_887_, 0);
v_k_913_ = lean_ctor_get(v_snd_887_, 5);
v___x_914_ = l_Lean_instBEqFVarId_beq(v_target_884_, v_fvarId_912_);
if (v___x_914_ == 0)
{
lean_object* v___x_916_; 
if (v_isShared_911_ == 0)
{
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_fst_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_887_);
v___x_916_ = v_reuseFailAlloc_918_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; 
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
else
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
lean_inc_ref(v_k_913_);
v___x_919_ = 1;
v___x_920_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_919_, v_snd_887_);
lean_dec_ref_known(v_snd_887_, 6);
v___x_921_ = lean_array_push(v_fst_908_, v___x_920_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_k_913_);
lean_ctor_set(v___x_910_, 0, v___x_921_);
v___x_923_ = v___x_910_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_913_);
v___x_923_ = v_reuseFailAlloc_925_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v_a_885_ = v___x_923_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_fst_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_946_; 
v_fst_928_ = lean_ctor_get(v_a_885_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_a_885_, 1);
lean_dec(v_unused_947_);
v___x_930_ = v_a_885_;
v_isShared_931_ = v_isSharedCheck_946_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_fst_928_);
lean_dec(v_a_885_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_946_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_fvarId_932_; lean_object* v_k_933_; uint8_t v___x_934_; 
v_fvarId_932_ = lean_ctor_get(v_snd_887_, 0);
v_k_933_ = lean_ctor_get(v_snd_887_, 3);
v___x_934_ = l_Lean_instBEqFVarId_beq(v_target_884_, v_fvarId_932_);
if (v___x_934_ == 0)
{
lean_object* v___x_936_; 
if (v_isShared_931_ == 0)
{
v___x_936_ = v___x_930_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_928_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_snd_887_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
else
{
uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
lean_inc_ref(v_k_933_);
v___x_939_ = 1;
v___x_940_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_939_, v_snd_887_);
lean_dec_ref_known(v_snd_887_, 4);
v___x_941_ = lean_array_push(v_fst_928_, v___x_940_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_k_933_);
lean_ctor_set(v___x_930_, 0, v___x_941_);
v___x_943_ = v___x_930_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_933_);
v___x_943_ = v_reuseFailAlloc_945_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
v_a_885_ = v___x_943_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_fst_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_fst_948_ = lean_ctor_get(v_a_885_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_a_885_, 1);
lean_dec(v_unused_957_);
v___x_950_ = v_a_885_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_fst_948_);
lean_dec(v_a_885_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_fst_948_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_snd_887_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_958_, lean_object* v_a_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_958_, v_a_959_);
lean_dec(v_target_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_962_, lean_object* v_k_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_sets_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_sets_969_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_sets_969_);
lean_ctor_set(v___x_970_, 1, v_k_963_);
v___x_971_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_962_, v___x_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_988_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_988_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_988_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_987_; 
v_fst_976_ = lean_ctor_get(v_a_972_, 0);
v_snd_977_ = lean_ctor_get(v_a_972_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_987_ == 0)
{
v___x_979_ = v_a_972_;
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_inc(v_fst_976_);
lean_dec(v_a_972_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_snd_977_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_982_);
v___x_984_ = v___x_974_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
else
{
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_989_, lean_object* v_k_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_989_, v_k_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_target_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_997_, lean_object* v_inst_998_, lean_object* v_a_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_997_, v_a_999_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_1006_, lean_object* v_inst_1007_, lean_object* v_a_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1006_, v_inst_1007_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v_target_1006_);
return v_res_1014_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_box(0);
v___x_1022_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_1023_ = l_Lean_Expr_const___override(v___x_1022_, v___x_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1024_, lean_object* v_mask_1025_, lean_object* v_origAllocId_1026_, lean_object* v_a_1027_, lean_object* v_b_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_a_1035_; uint8_t v___x_1039_; 
v___x_1039_ = lean_nat_dec_lt(v_a_1027_, v_upperBound_1024_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v_a_1027_);
lean_dec(v_origAllocId_1026_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_b_1028_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_array_fget_borrowed(v_mask_1025_, v_a_1027_);
if (lean_obj_tag(v___x_1041_) == 0)
{
uint8_t v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = 1;
v___x_1043_ = 0;
v___x_1044_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_1045_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1044_, v___y_1030_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_1026_);
lean_inc(v_a_1027_);
v___x_1048_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1027_);
lean_ctor_set(v___x_1048_, 1, v_origAllocId_1026_);
v___x_1049_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1042_, v_a_1046_, v___x_1047_, v___x_1048_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v_fvarId_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v_fvarId_1051_ = lean_ctor_get(v_a_1050_, 0);
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = lean_box(0);
lean_inc(v_fvarId_1051_);
v___x_1054_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1054_, 0, v_fvarId_1051_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
lean_ctor_set(v___x_1054_, 2, v___x_1053_);
lean_ctor_set(v___x_1054_, 3, v_b_1028_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*4, v___x_1039_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*4 + 1, v___x_1043_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1050_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v_a_1035_ = v___x_1055_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_b_1028_);
lean_dec(v_a_1027_);
lean_dec(v_origAllocId_1026_);
v_a_1056_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1049_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1049_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_b_1028_);
lean_dec(v_a_1027_);
lean_dec(v_origAllocId_1026_);
v_a_1064_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1045_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1045_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
v_a_1035_ = v_b_1028_;
goto v___jp_1034_;
}
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_nat_add(v_a_1027_, v___x_1036_);
lean_dec(v_a_1027_);
v_a_1027_ = v___x_1037_;
v_b_1028_ = v_a_1035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1072_, lean_object* v_mask_1073_, lean_object* v_origAllocId_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1072_, v_mask_1073_, v_origAllocId_1074_, v_a_1075_, v_b_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v_mask_1073_);
lean_dec(v_upperBound_1072_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1083_, lean_object* v_mask_1084_, lean_object* v_resetJpId_1085_, lean_object* v_isSharedId_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_code_1100_; lean_object* v___x_1101_; 
lean_inc(v_origAllocId_1083_);
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_origAllocId_1083_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_isSharedId_1086_);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_array_get_size(v_mask_1084_);
v___x_1096_ = lean_unsigned_to_nat(2u);
v___x_1097_ = lean_mk_empty_array_with_capacity(v___x_1096_);
v___x_1098_ = lean_array_push(v___x_1097_, v___x_1092_);
v___x_1099_ = lean_array_push(v___x_1098_, v___x_1093_);
v_code_1100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1100_, 0, v_resetJpId_1085_);
lean_ctor_set(v_code_1100_, 1, v___x_1099_);
v___x_1101_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1095_, v_mask_1084_, v_origAllocId_1083_, v___x_1094_, v_code_1100_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1102_, lean_object* v_mask_1103_, lean_object* v_resetJpId_1104_, lean_object* v_isSharedId_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1102_, v_mask_1103_, v_resetJpId_1104_, v_isSharedId_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_mask_1103_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1112_, lean_object* v_mask_1113_, lean_object* v_origAllocId_1114_, lean_object* v_inst_1115_, lean_object* v_R_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_, lean_object* v_c_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1112_, v_mask_1113_, v_origAllocId_1114_, v_a_1117_, v_b_1118_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1126_, lean_object* v_mask_1127_, lean_object* v_origAllocId_1128_, lean_object* v_inst_1129_, lean_object* v_R_1130_, lean_object* v_a_1131_, lean_object* v_b_1132_, lean_object* v_c_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1126_, v_mask_1127_, v_origAllocId_1128_, v_inst_1129_, v_R_1130_, v_a_1131_, v_b_1132_, v_c_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v_mask_1127_);
lean_dec(v_upperBound_1126_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v_a_1146_; uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_b_1143_);
return v___x_1151_;
}
else
{
lean_object* v_a_1152_; 
v_a_1152_ = lean_array_uget_borrowed(v_as_1140_, v_i_1142_);
if (lean_obj_tag(v_a_1152_) == 1)
{
lean_object* v_val_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; 
v_val_1153_ = lean_ctor_get(v_a_1152_, 0);
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = 0;
lean_inc(v_val_1153_);
v___x_1156_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1156_, 0, v_val_1153_);
lean_ctor_set(v___x_1156_, 1, v___x_1154_);
lean_ctor_set(v___x_1156_, 2, v_b_1143_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3, v___x_1150_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*3 + 1, v___x_1155_);
v_a_1146_ = v___x_1156_;
goto v___jp_1145_;
}
else
{
v_a_1146_ = v_b_1143_;
goto v___jp_1145_;
}
}
v___jp_1145_:
{
size_t v___x_1147_; size_t v___x_1148_; 
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_add(v_i_1142_, v___x_1147_);
v_i_1142_ = v___x_1148_;
v_b_1143_ = v_a_1146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1157_, lean_object* v_sz_1158_, lean_object* v_i_1159_, lean_object* v_b_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1158_);
lean_dec(v_sz_1158_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1157_, v_sz_boxed_1162_, v_i_boxed_1163_, v_b_1160_);
lean_dec_ref(v_as_1157_);
return v_res_1164_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_unsigned_to_nat(2u);
v___x_1167_ = lean_mk_empty_array_with_capacity(v___x_1166_);
v___x_1168_ = lean_array_push(v___x_1167_, v___x_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1169_, lean_object* v_mask_1170_, lean_object* v_resetJpId_1171_, lean_object* v_isSharedId_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_code_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v_code_1186_; size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_isSharedId_1172_);
v___x_1179_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1180_ = lean_array_push(v___x_1179_, v___x_1178_);
v_code_1181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1181_, 0, v_resetJpId_1171_);
lean_ctor_set(v_code_1181_, 1, v___x_1180_);
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = 1;
v___x_1184_ = 0;
v___x_1185_ = lean_box(0);
v_code_1186_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_code_1186_, 0, v_origAllocId_1169_);
lean_ctor_set(v_code_1186_, 1, v___x_1182_);
lean_ctor_set(v_code_1186_, 2, v___x_1185_);
lean_ctor_set(v_code_1186_, 3, v_code_1181_);
lean_ctor_set_uint8(v_code_1186_, sizeof(void*)*4, v___x_1183_);
lean_ctor_set_uint8(v_code_1186_, sizeof(void*)*4 + 1, v___x_1184_);
v_sz_1187_ = lean_array_size(v_mask_1170_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1170_, v_sz_1187_, v___x_1188_, v_code_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* v_origAllocId_1190_, lean_object* v_mask_1191_, lean_object* v_resetJpId_1192_, lean_object* v_isSharedId_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1190_, v_mask_1191_, v_resetJpId_1192_, v_isSharedId_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec_ref(v_mask_1191_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* v_as_1200_, size_t v_sz_1201_, size_t v_i_1202_, lean_object* v_b_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1200_, v_sz_1201_, v_i_1202_, v_b_1203_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* v_as_1210_, lean_object* v_sz_1211_, lean_object* v_i_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
size_t v_sz_boxed_1219_; size_t v_i_boxed_1220_; lean_object* v_res_1221_; 
v_sz_boxed_1219_ = lean_unbox_usize(v_sz_1211_);
lean_dec(v_sz_1211_);
v_i_boxed_1220_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_res_1221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1210_, v_sz_boxed_1219_, v_i_boxed_1220_, v_b_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_as_1210_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1222_, lean_object* v_args_1223_, lean_object* v_origAllocId_1224_, lean_object* v_resetTokenId_1225_, lean_object* v_a_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_a_1231_; uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_lt(v_a_1226_, v_upperBound_1222_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec(v_a_1226_);
lean_dec(v_resetTokenId_1225_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_b_1227_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_array_fget_borrowed(v_args_1223_, v_a_1226_);
v___x_1238_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1224_, v_a_1226_, v___x_1237_, v___y_1228_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; uint8_t v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_unbox(v_a_1239_);
lean_dec(v_a_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v___x_1237_);
lean_inc(v_a_1226_);
lean_inc(v_resetTokenId_1225_);
v___x_1241_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1241_, 0, v_resetTokenId_1225_);
lean_ctor_set(v___x_1241_, 1, v_a_1226_);
lean_ctor_set(v___x_1241_, 2, v___x_1237_);
lean_ctor_set(v___x_1241_, 3, v_b_1227_);
v_a_1231_ = v___x_1241_;
goto v___jp_1230_;
}
else
{
v_a_1231_ = v_b_1227_;
goto v___jp_1230_;
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_b_1227_);
lean_dec(v_a_1226_);
lean_dec(v_resetTokenId_1225_);
v_a_1242_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1238_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_a_1226_, v___x_1232_);
lean_dec(v_a_1226_);
v_a_1226_ = v___x_1233_;
v_b_1227_ = v_a_1231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1250_, lean_object* v_args_1251_, lean_object* v_origAllocId_1252_, lean_object* v_resetTokenId_1253_, lean_object* v_a_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1250_, v_args_1251_, v_origAllocId_1252_, v_resetTokenId_1253_, v_a_1254_, v_b_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec(v_origAllocId_1252_);
lean_dec_ref(v_args_1251_);
lean_dec(v_upperBound_1250_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* v_resetTokenId_1259_, lean_object* v_info_1260_, uint8_t v_update_1261_, lean_object* v_args_1262_, lean_object* v_contJpId_1263_, lean_object* v_origAllocId_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_code_1276_; lean_object* v___x_1277_; 
lean_inc_n(v_resetTokenId_1259_, 2);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_resetTokenId_1259_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_array_get_size(v_args_1262_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_mk_empty_array_with_capacity(v___x_1273_);
v___x_1275_ = lean_array_push(v___x_1274_, v___x_1270_);
v_code_1276_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1276_, 0, v_contJpId_1263_);
lean_ctor_set(v_code_1276_, 1, v___x_1275_);
v___x_1277_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_1272_, v_args_1262_, v_origAllocId_1264_, v_resetTokenId_1259_, v___x_1271_, v_code_1276_, v_a_1266_);
if (lean_obj_tag(v___x_1277_) == 0)
{
if (v_update_1261_ == 0)
{
lean_dec(v_resetTokenId_1259_);
return v___x_1277_;
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1287_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_cidx_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v_cidx_1282_ = lean_ctor_get(v_info_1260_, 1);
lean_inc(v_cidx_1282_);
v___x_1283_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1283_, 0, v_resetTokenId_1259_);
lean_ctor_set(v___x_1283_, 1, v_cidx_1282_);
lean_ctor_set(v___x_1283_, 2, v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_dec(v_resetTokenId_1259_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* v_resetTokenId_1288_, lean_object* v_info_1289_, lean_object* v_update_1290_, lean_object* v_args_1291_, lean_object* v_contJpId_1292_, lean_object* v_origAllocId_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
uint8_t v_update_boxed_1299_; lean_object* v_res_1300_; 
v_update_boxed_1299_ = lean_unbox(v_update_1290_);
v_res_1300_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1288_, v_info_1289_, v_update_boxed_1299_, v_args_1291_, v_contJpId_1292_, v_origAllocId_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_origAllocId_1293_);
lean_dec_ref(v_args_1291_);
lean_dec_ref(v_info_1289_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* v_upperBound_1301_, lean_object* v_args_1302_, lean_object* v_origAllocId_1303_, lean_object* v_resetTokenId_1304_, lean_object* v_inst_1305_, lean_object* v_R_1306_, lean_object* v_a_1307_, lean_object* v_b_1308_, lean_object* v_c_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1301_, v_args_1302_, v_origAllocId_1303_, v_resetTokenId_1304_, v_a_1307_, v_b_1308_, v___y_1311_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1316_, lean_object* v_args_1317_, lean_object* v_origAllocId_1318_, lean_object* v_resetTokenId_1319_, lean_object* v_inst_1320_, lean_object* v_R_1321_, lean_object* v_a_1322_, lean_object* v_b_1323_, lean_object* v_c_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1316_, v_args_1317_, v_origAllocId_1318_, v_resetTokenId_1319_, v_inst_1320_, v_R_1321_, v_a_1322_, v_b_1323_, v_c_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v_origAllocId_1318_);
lean_dec_ref(v_args_1317_);
lean_dec(v_upperBound_1316_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* v_decl_1334_, lean_object* v_info_1335_, lean_object* v_args_1336_, lean_object* v_contJpId_1337_, lean_object* v_selfSets_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
v___x_1345_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1344_, v_a_1340_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_type_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v_type_1347_ = lean_ctor_get(v_decl_1334_, 2);
lean_inc_ref(v_type_1347_);
lean_dec_ref(v_decl_1334_);
v___x_1348_ = 1;
v___x_1349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_info_1335_);
lean_ctor_set(v___x_1349_, 1, v_args_1336_);
v___x_1350_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1348_, v_a_1346_, v_type_1347_, v___x_1349_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_fvarId_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1368_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v_fvarId_1352_ = lean_ctor_get(v_a_1351_, 0);
lean_inc_n(v_fvarId_1352_, 2);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_fvarId_1352_);
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_mk_empty_array_with_capacity(v___x_1354_);
v___x_1356_ = lean_array_push(v___x_1355_, v___x_1353_);
v___x_1357_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_contJpId_1337_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1352_, v_selfSets_1338_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1368_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1363_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1359_, v___x_1357_);
lean_dec(v_a_1359_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1351_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1364_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_selfSets_1338_);
lean_dec(v_contJpId_1337_);
v_a_1369_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1350_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1350_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_selfSets_1338_);
lean_dec(v_contJpId_1337_);
lean_dec_ref(v_args_1336_);
lean_dec_ref(v_info_1335_);
lean_dec_ref(v_decl_1334_);
v_a_1377_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1345_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1345_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* v_decl_1385_, lean_object* v_info_1386_, lean_object* v_args_1387_, lean_object* v_contJpId_1388_, lean_object* v_selfSets_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1385_, v_info_1386_, v_args_1387_, v_contJpId_1388_, v_selfSets_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* v_alt_1396_, lean_object* v_f_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___y_1404_; 
switch(lean_obj_tag(v_alt_1396_))
{
case 0:
{
lean_object* v_code_1423_; 
v_code_1423_ = lean_ctor_get(v_alt_1396_, 2);
lean_inc_ref(v_code_1423_);
v___y_1404_ = v_code_1423_;
goto v___jp_1403_;
}
case 1:
{
lean_object* v_code_1424_; 
v_code_1424_ = lean_ctor_get(v_alt_1396_, 1);
lean_inc_ref(v_code_1424_);
v___y_1404_ = v_code_1424_;
goto v___jp_1403_;
}
default: 
{
lean_object* v_code_1425_; 
v_code_1425_ = lean_ctor_get(v_alt_1396_, 0);
lean_inc_ref(v_code_1425_);
v___y_1404_ = v_code_1425_;
goto v___jp_1403_;
}
}
v___jp_1403_:
{
lean_object* v___x_1405_; 
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
v___x_1405_ = lean_apply_6(v_f_1397_, v___y_1404_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, lean_box(0));
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1396_, v_a_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v_alt_1396_);
v_a_1415_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1405_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1405_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* v_alt_1426_, lean_object* v_f_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1426_, v_f_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t v_pu_1434_, lean_object* v_alt_1435_, lean_object* v_f_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1435_, v_f_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* v_pu_1443_, lean_object* v_alt_1444_, lean_object* v_f_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_pu_boxed_1451_; lean_object* v_res_1452_; 
v_pu_boxed_1451_ = lean_unbox(v_pu_1443_);
v_res_1452_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_1451_, v_alt_1444_, v_f_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1452_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_toApplicative_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1495_; 
v___x_1460_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1461_ = l_StateRefT_x27_instMonad___redArg(v___x_1460_);
v_toApplicative_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v___x_1461_, 1);
lean_dec(v_unused_1496_);
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1495_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_toApplicative_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1495_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_toFunctor_1466_; lean_object* v_toSeq_1467_; lean_object* v_toSeqLeft_1468_; lean_object* v_toSeqRight_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1493_; 
v_toFunctor_1466_ = lean_ctor_get(v_toApplicative_1462_, 0);
v_toSeq_1467_ = lean_ctor_get(v_toApplicative_1462_, 2);
v_toSeqLeft_1468_ = lean_ctor_get(v_toApplicative_1462_, 3);
v_toSeqRight_1469_ = lean_ctor_get(v_toApplicative_1462_, 4);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_toApplicative_1462_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_toApplicative_1462_, 1);
lean_dec(v_unused_1494_);
v___x_1471_ = v_toApplicative_1462_;
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_toSeqRight_1469_);
lean_inc(v_toSeqLeft_1468_);
lean_inc(v_toSeq_1467_);
lean_inc(v_toFunctor_1466_);
lean_dec(v_toApplicative_1462_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1493_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___f_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___x_1482_; 
v___f_1473_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1474_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1466_);
v___f_1475_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1475_, 0, v_toFunctor_1466_);
v___f_1476_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1476_, 0, v_toFunctor_1466_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___f_1475_);
lean_ctor_set(v___x_1477_, 1, v___f_1476_);
v___f_1478_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1478_, 0, v_toSeqRight_1469_);
v___f_1479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1479_, 0, v_toSeqLeft_1468_);
v___f_1480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1480_, 0, v_toSeq_1467_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v___f_1478_);
lean_ctor_set(v___x_1471_, 3, v___f_1479_);
lean_ctor_set(v___x_1471_, 2, v___f_1480_);
lean_ctor_set(v___x_1471_, 1, v___f_1473_);
lean_ctor_set(v___x_1471_, 0, v___x_1477_);
v___x_1482_ = v___x_1471_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___f_1473_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v___f_1480_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v___f_1479_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v___f_1478_);
v___x_1482_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___f_1474_);
lean_ctor_set(v___x_1464_, 0, v___x_1482_);
v___x_1484_ = v___x_1464_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___f_1474_);
v___x_1484_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___f_1488_; lean_object* v___x_6385__overap_1489_; lean_object* v___x_1490_; 
v___x_1485_ = l_StateRefT_x27_instMonad___redArg(v___x_1484_);
v___x_1486_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1487_ = l_instInhabitedOfMonad___redArg(v___x_1485_, v___x_1486_);
v___f_1488_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1488_, 0, v___x_1487_);
v___x_6385__overap_1489_ = lean_panic_fn_borrowed(v___f_1488_, v_msg_1454_);
lean_dec_ref(v___f_1488_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
v___x_1490_ = lean_apply_5(v___x_6385__overap_1489_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, lean_box(0));
return v___x_1490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1503_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1512_ = l_Lean_Expr_const___override(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1513_, lean_object* v_origAllocId_1514_, lean_object* v_isSharedId_1515_, lean_object* v_resultType_1516_, lean_object* v_x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1513_, v_origAllocId_1514_, v_isSharedId_1515_, v_resultType_1516_, v_x_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1524_, lean_object* v_origAllocId_1525_, lean_object* v_isSharedId_1526_, lean_object* v_resultType_1527_, lean_object* v_i_1528_, lean_object* v_as_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = lean_array_get_size(v_as_1529_);
v___x_1536_ = lean_nat_dec_lt(v_i_1528_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_i_1528_);
lean_dec_ref(v_resultType_1527_);
lean_dec(v_isSharedId_1526_);
lean_dec(v_origAllocId_1525_);
lean_dec(v_resetTokenId_1524_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_as_1529_);
return v___x_1537_;
}
else
{
lean_object* v___f_1538_; lean_object* v_a_1539_; lean_object* v___x_1540_; 
lean_inc_ref(v_resultType_1527_);
lean_inc(v_isSharedId_1526_);
lean_inc(v_origAllocId_1525_);
lean_inc(v_resetTokenId_1524_);
v___f_1538_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1538_, 0, v_resetTokenId_1524_);
lean_closure_set(v___f_1538_, 1, v_origAllocId_1525_);
lean_closure_set(v___f_1538_, 2, v_isSharedId_1526_);
lean_closure_set(v___f_1538_, 3, v_resultType_1527_);
v_a_1539_ = lean_array_fget_borrowed(v_as_1529_, v_i_1528_);
lean_inc(v_a_1539_);
v___x_1540_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1539_, v___f_1538_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; size_t v___x_1542_; size_t v___x_1543_; uint8_t v___x_1544_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = lean_ptr_addr(v_a_1539_);
v___x_1543_ = lean_ptr_addr(v_a_1541_);
v___x_1544_ = lean_usize_dec_eq(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_add(v_i_1528_, v___x_1545_);
v___x_1547_ = lean_array_fset(v_as_1529_, v_i_1528_, v_a_1541_);
lean_dec(v_i_1528_);
v_i_1528_ = v___x_1546_;
v_as_1529_ = v___x_1547_;
goto _start;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v_a_1541_);
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_add(v_i_1528_, v___x_1549_);
lean_dec(v_i_1528_);
v_i_1528_ = v___x_1550_;
goto _start;
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_as_1529_);
lean_dec(v_i_1528_);
lean_dec_ref(v_resultType_1527_);
lean_dec(v_isSharedId_1526_);
lean_dec(v_origAllocId_1525_);
lean_dec(v_resetTokenId_1524_);
v_a_1552_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1540_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1540_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1562_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1563_ = lean_unsigned_to_nat(6u);
v___x_1564_ = lean_unsigned_to_nat(208u);
v___x_1565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1566_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_1567_ = l_mkPanicMessageWithDecl(v___x_1566_, v___x_1565_, v___x_1564_, v___x_1563_, v___x_1562_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1568_, lean_object* v_code_1569_, lean_object* v_origAllocId_1570_, lean_object* v_isSharedId_1571_, lean_object* v_currentRetType_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
switch(lean_obj_tag(v_code_1569_))
{
case 0:
{
lean_object* v_decl_1578_; lean_object* v_value_1579_; 
v_decl_1578_ = lean_ctor_get(v_code_1569_, 0);
v_value_1579_ = lean_ctor_get(v_decl_1578_, 3);
lean_inc(v_value_1579_);
if (lean_obj_tag(v_value_1579_) == 12)
{
lean_object* v_k_1580_; lean_object* v_fvarId_1581_; lean_object* v_binderName_1582_; lean_object* v_type_1583_; lean_object* v_var_1584_; lean_object* v_i_1585_; uint8_t v_updateHeader_1586_; lean_object* v_args_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1703_; 
v_k_1580_ = lean_ctor_get(v_code_1569_, 1);
v_fvarId_1581_ = lean_ctor_get(v_decl_1578_, 0);
v_binderName_1582_ = lean_ctor_get(v_decl_1578_, 1);
v_type_1583_ = lean_ctor_get(v_decl_1578_, 2);
v_var_1584_ = lean_ctor_get(v_value_1579_, 0);
v_i_1585_ = lean_ctor_get(v_value_1579_, 1);
v_updateHeader_1586_ = lean_ctor_get_uint8(v_value_1579_, sizeof(void*)*3);
v_args_1587_ = lean_ctor_get(v_value_1579_, 2);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_value_1579_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1589_ = v_value_1579_;
v_isShared_1590_ = v_isSharedCheck_1703_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_args_1587_);
lean_inc(v_i_1585_);
lean_inc(v_var_1584_);
lean_dec(v_value_1579_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1703_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
uint8_t v___x_1591_; 
v___x_1591_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1568_, v_var_1584_);
lean_dec(v_var_1584_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_del_object(v___x_1589_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
lean_inc_ref(v_k_1580_);
v___x_1592_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1580_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1615_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
size_t v___x_1597_; size_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = lean_ptr_addr(v_k_1580_);
v___x_1598_ = lean_ptr_addr(v_a_1593_);
v___x_1599_ = lean_usize_dec_eq(v___x_1597_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1609_; 
lean_inc_ref(v_decl_1578_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1610_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1611_);
v___x_1601_ = v_code_1569_;
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v_code_1569_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v_a_1593_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_decl_1578_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_a_1593_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1604_);
v___x_1606_ = v___x_1595_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v___x_1613_; 
lean_dec(v_a_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_code_1569_);
v___x_1613_ = v___x_1595_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_code_1569_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 2);
return v___x_1592_;
}
}
else
{
lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1700_; 
lean_inc_ref(v_k_1580_);
lean_inc_ref(v_decl_1578_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1701_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1702_);
v___x_1617_ = v_code_1569_;
v_isShared_1618_ = v_isSharedCheck_1700_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v_code_1569_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1700_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = 0;
v___x_1620_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1581_, v_k_1580_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1624_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_fst_1622_);
v_snd_1623_ = lean_ctor_get(v_a_1621_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1621_);
v___x_1624_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1570_, v_fst_1622_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_fst_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_fst_1626_; lean_object* v_snd_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_fst_1626_ = lean_ctor_get(v_a_1625_, 0);
lean_inc(v_fst_1626_);
v_snd_1627_ = lean_ctor_get(v_a_1625_, 1);
lean_inc(v_snd_1627_);
lean_dec(v_a_1625_);
v___x_1628_ = 1;
v___x_1629_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1627_, v_snd_1623_);
lean_dec(v_snd_1627_);
lean_inc_ref(v_type_1583_);
lean_inc(v_binderName_1582_);
lean_inc(v_fvarId_1581_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 0);
lean_ctor_set(v___x_1589_, 2, v_type_1583_);
lean_ctor_set(v___x_1589_, 1, v_binderName_1582_);
lean_ctor_set(v___x_1589_, 0, v_fvarId_1581_);
v___x_1631_ = v___x_1589_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_fvarId_1581_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_binderName_1582_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_type_1583_);
v___x_1631_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*3, v___x_1619_);
v___x_1632_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1633_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1632_, v_a_1574_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1635_);
v___x_1637_ = lean_array_push(v___x_1636_, v___x_1631_);
lean_inc_ref(v_currentRetType_1572_);
v___x_1638_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1628_, v_a_1634_, v_currentRetType_1572_, v___x_1637_, v___x_1629_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v_fvarId_1640_; lean_object* v___x_1641_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v_fvarId_1640_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_fvarId_1640_);
lean_inc_ref(v_args_1587_);
lean_inc_ref(v_i_1585_);
lean_inc_ref(v_decl_1578_);
v___x_1641_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1578_, v_i_1585_, v_args_1587_, v_fvarId_1640_, v_fst_1626_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
lean_inc(v_fvarId_1640_);
v___x_1643_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1568_, v_i_1585_, v_updateHeader_1586_, v_args_1587_, v_fvarId_1640_, v_origAllocId_1570_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_origAllocId_1570_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1628_, v_decl_1578_, v_a_1574_);
lean_dec_ref(v_decl_1578_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref_known(v___x_1645_, 1);
v___x_1646_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1647_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1571_, v___x_1646_, v_currentRetType_1572_, v_a_1642_, v_a_1644_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1658_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 2);
lean_ctor_set(v___x_1617_, 1, v_a_1648_);
lean_ctor_set(v___x_1617_, 0, v_a_1639_);
v___x_1653_ = v___x_1617_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1639_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_dec(v_a_1639_);
lean_del_object(v___x_1617_);
return v___x_1647_;
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_a_1644_);
lean_dec(v_a_1642_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
v_a_1659_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1645_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1645_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_dec(v_a_1642_);
lean_dec(v_a_1639_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_decl_1578_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
return v___x_1643_;
}
}
else
{
lean_dec(v_a_1639_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
lean_dec_ref(v_decl_1578_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
return v___x_1641_;
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_fst_1626_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
lean_dec_ref(v_decl_1578_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
v_a_1667_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1638_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1638_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
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
lean_dec_ref(v___x_1631_);
lean_dec_ref(v___x_1629_);
lean_dec(v_fst_1626_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
lean_dec_ref(v_decl_1578_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
v_a_1675_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1633_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1633_);
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
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_snd_1623_);
lean_del_object(v___x_1617_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
lean_dec_ref(v_decl_1578_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
v_a_1684_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1624_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1624_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_del_object(v___x_1617_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_args_1587_);
lean_dec_ref(v_i_1585_);
lean_dec_ref(v_decl_1578_);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
v_a_1692_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1620_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1620_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
}
else
{
lean_object* v_k_1704_; lean_object* v___x_1705_; 
lean_dec(v_value_1579_);
v_k_1704_ = lean_ctor_get(v_code_1569_, 1);
lean_inc_ref(v_k_1704_);
v___x_1705_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1704_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1728_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1728_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1728_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
size_t v___x_1710_; size_t v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = lean_ptr_addr(v_k_1704_);
v___x_1711_ = lean_ptr_addr(v_a_1706_);
v___x_1712_ = lean_usize_dec_eq(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1722_; 
lean_inc_ref(v_decl_1578_);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; lean_object* v_unused_1724_; 
v_unused_1723_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1723_);
v_unused_1724_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1724_);
v___x_1714_ = v_code_1569_;
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v_code_1569_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_a_1706_);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_decl_1578_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_a_1706_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1717_);
v___x_1719_ = v___x_1708_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v___x_1726_; 
lean_dec(v_a_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v_code_1569_);
v___x_1726_ = v___x_1708_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_code_1569_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 2);
return v___x_1705_;
}
}
}
case 2:
{
lean_object* v_decl_1729_; lean_object* v_k_1730_; lean_object* v_params_1731_; lean_object* v_type_1732_; lean_object* v_value_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; 
v_decl_1729_ = lean_ctor_get(v_code_1569_, 0);
v_k_1730_ = lean_ctor_get(v_code_1569_, 1);
v_params_1731_ = lean_ctor_get(v_decl_1729_, 2);
v_type_1732_ = lean_ctor_get(v_decl_1729_, 3);
v_value_1733_ = lean_ctor_get(v_decl_1729_, 4);
v___x_1734_ = 1;
lean_inc_ref(v_type_1732_);
lean_inc(v_isSharedId_1571_);
lean_inc(v_origAllocId_1570_);
lean_inc_ref(v_value_1733_);
lean_inc(v_resetTokenId_1568_);
v___x_1735_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_value_1733_, v_origAllocId_1570_, v_isSharedId_1571_, v_type_1732_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
lean_inc_ref(v_params_1731_);
lean_inc_ref(v_type_1732_);
lean_inc_ref(v_decl_1729_);
v___x_1737_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1734_, v_decl_1729_, v_type_1732_, v_params_1731_, v_a_1736_, v_a_1574_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1739_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
lean_inc_ref(v_k_1730_);
v___x_1739_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1730_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1777_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1777_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1777_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
size_t v___x_1744_; size_t v___x_1745_; uint8_t v___x_1746_; 
v___x_1744_ = lean_ptr_addr(v_k_1730_);
v___x_1745_ = lean_ptr_addr(v_a_1740_);
v___x_1746_ = lean_usize_dec_eq(v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1756_; 
v_isSharedCheck_1756_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; lean_object* v_unused_1758_; 
v_unused_1757_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1758_);
v___x_1748_ = v_code_1569_;
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_code_1569_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_a_1740_);
lean_ctor_set(v___x_1748_, 0, v_a_1738_);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1738_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_a_1740_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1751_);
v___x_1753_ = v___x_1742_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = lean_ptr_addr(v_decl_1729_);
v___x_1760_ = lean_ptr_addr(v_a_1738_);
v___x_1761_ = lean_usize_dec_eq(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1771_; 
v_isSharedCheck_1771_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; lean_object* v_unused_1773_; 
v_unused_1772_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1773_);
v___x_1763_ = v_code_1569_;
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
else
{
lean_dec(v_code_1569_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v_a_1740_);
lean_ctor_set(v___x_1763_, 0, v_a_1738_);
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1738_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_a_1740_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1766_);
v___x_1768_ = v___x_1742_;
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
}
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_a_1740_);
lean_dec(v_a_1738_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v_code_1569_);
v___x_1775_ = v___x_1742_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_code_1569_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_dec(v_a_1738_);
lean_dec_ref_known(v_code_1569_, 2);
return v___x_1739_;
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref_known(v_code_1569_, 2);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
v_a_1778_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1737_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1737_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 2);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
return v___x_1735_;
}
}
case 4:
{
lean_object* v_cases_1786_; lean_object* v_typeName_1787_; lean_object* v_resultType_1788_; lean_object* v_discr_1789_; lean_object* v_alts_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v_currentRetType_1572_);
v_cases_1786_ = lean_ctor_get(v_code_1569_, 0);
lean_inc_ref(v_cases_1786_);
v_typeName_1787_ = lean_ctor_get(v_cases_1786_, 0);
v_resultType_1788_ = lean_ctor_get(v_cases_1786_, 1);
v_discr_1789_ = lean_ctor_get(v_cases_1786_, 2);
v_alts_1790_ = lean_ctor_get(v_cases_1786_, 3);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_cases_1786_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1792_ = v_cases_1786_;
v_isShared_1793_ = v_isSharedCheck_1829_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_alts_1790_);
lean_inc(v_discr_1789_);
lean_inc(v_resultType_1788_);
lean_inc(v_typeName_1787_);
lean_dec(v_cases_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1829_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1790_);
lean_inc_ref(v_resultType_1788_);
v___x_1795_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1568_, v_origAllocId_1570_, v_isSharedId_1571_, v_resultType_1788_, v___x_1794_, v_alts_1790_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1820_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
size_t v___x_1800_; size_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1800_ = lean_ptr_addr(v_alts_1790_);
lean_dec_ref(v_alts_1790_);
v___x_1801_ = lean_ptr_addr(v_a_1796_);
v___x_1802_ = lean_usize_dec_eq(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1815_; 
v_isSharedCheck_1815_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1816_);
v___x_1804_ = v_code_1569_;
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
else
{
lean_dec(v_code_1569_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1815_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 3, v_a_1796_);
v___x_1807_ = v___x_1792_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_typeName_1787_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_resultType_1788_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_discr_1789_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_a_1796_);
v___x_1807_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1807_);
v___x_1809_ = v___x_1804_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1809_);
v___x_1811_ = v___x_1798_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_a_1796_);
lean_del_object(v___x_1792_);
lean_dec(v_discr_1789_);
lean_dec_ref(v_resultType_1788_);
lean_dec(v_typeName_1787_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v_code_1569_);
v___x_1818_ = v___x_1798_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_code_1569_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_del_object(v___x_1792_);
lean_dec_ref(v_alts_1790_);
lean_dec(v_discr_1789_);
lean_dec_ref(v_resultType_1788_);
lean_dec(v_typeName_1787_);
lean_dec_ref_known(v_code_1569_, 1);
v_a_1821_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1795_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1795_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1830_; lean_object* v_i_1831_; lean_object* v_y_1832_; lean_object* v_k_1833_; lean_object* v___x_1834_; 
v_fvarId_1830_ = lean_ctor_get(v_code_1569_, 0);
v_i_1831_ = lean_ctor_get(v_code_1569_, 1);
v_y_1832_ = lean_ctor_get(v_code_1569_, 2);
v_k_1833_ = lean_ctor_get(v_code_1569_, 3);
lean_inc_ref(v_k_1833_);
v___x_1834_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1833_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1859_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1859_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1859_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
size_t v___x_1839_; size_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_ptr_addr(v_k_1833_);
v___x_1840_ = lean_ptr_addr(v_a_1835_);
v___x_1841_ = lean_usize_dec_eq(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1851_; 
lean_inc(v_y_1832_);
lean_inc(v_i_1831_);
lean_inc(v_fvarId_1830_);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; 
v_unused_1852_ = lean_ctor_get(v_code_1569_, 3);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_code_1569_, 2);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1855_);
v___x_1843_ = v_code_1569_;
v_isShared_1844_ = v_isSharedCheck_1851_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v_code_1569_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1851_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 3, v_a_1835_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_fvarId_1830_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_i_1831_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_y_1832_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_a_1835_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1846_);
v___x_1848_ = v___x_1837_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v___x_1857_; 
lean_dec(v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v_code_1569_);
v___x_1857_ = v___x_1837_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_code_1569_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 4);
return v___x_1834_;
}
}
case 8:
{
lean_object* v_fvarId_1860_; lean_object* v_i_1861_; lean_object* v_y_1862_; lean_object* v_k_1863_; lean_object* v___x_1864_; 
v_fvarId_1860_ = lean_ctor_get(v_code_1569_, 0);
v_i_1861_ = lean_ctor_get(v_code_1569_, 1);
v_y_1862_ = lean_ctor_get(v_code_1569_, 2);
v_k_1863_ = lean_ctor_get(v_code_1569_, 3);
lean_inc_ref(v_k_1863_);
v___x_1864_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1863_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1889_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1889_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1889_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
size_t v___x_1869_; size_t v___x_1870_; uint8_t v___x_1871_; 
v___x_1869_ = lean_ptr_addr(v_k_1863_);
v___x_1870_ = lean_ptr_addr(v_a_1865_);
v___x_1871_ = lean_usize_dec_eq(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1881_; 
lean_inc(v_y_1862_);
lean_inc(v_i_1861_);
lean_inc(v_fvarId_1860_);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; lean_object* v_unused_1885_; 
v_unused_1882_ = lean_ctor_get(v_code_1569_, 3);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_code_1569_, 2);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1884_);
v_unused_1885_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1885_);
v___x_1873_ = v_code_1569_;
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
else
{
lean_dec(v_code_1569_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 3, v_a_1865_);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_fvarId_1860_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_i_1861_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_y_1862_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_a_1865_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1876_);
v___x_1878_ = v___x_1867_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v___x_1887_; 
lean_dec(v_a_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_code_1569_);
v___x_1887_ = v___x_1867_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_code_1569_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 4);
return v___x_1864_;
}
}
case 9:
{
lean_object* v_fvarId_1890_; lean_object* v_i_1891_; lean_object* v_offset_1892_; lean_object* v_y_1893_; lean_object* v_ty_1894_; lean_object* v_k_1895_; lean_object* v___x_1896_; 
v_fvarId_1890_ = lean_ctor_get(v_code_1569_, 0);
v_i_1891_ = lean_ctor_get(v_code_1569_, 1);
v_offset_1892_ = lean_ctor_get(v_code_1569_, 2);
v_y_1893_ = lean_ctor_get(v_code_1569_, 3);
v_ty_1894_ = lean_ctor_get(v_code_1569_, 4);
v_k_1895_ = lean_ctor_get(v_code_1569_, 5);
lean_inc_ref(v_k_1895_);
v___x_1896_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1895_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1923_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1923_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1923_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
size_t v___x_1901_; size_t v___x_1902_; uint8_t v___x_1903_; 
v___x_1901_ = lean_ptr_addr(v_k_1895_);
v___x_1902_ = lean_ptr_addr(v_a_1897_);
v___x_1903_ = lean_usize_dec_eq(v___x_1901_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1913_; 
lean_inc_ref(v_ty_1894_);
lean_inc(v_y_1893_);
lean_inc(v_offset_1892_);
lean_inc(v_i_1891_);
lean_inc(v_fvarId_1890_);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; lean_object* v_unused_1915_; lean_object* v_unused_1916_; lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; 
v_unused_1914_ = lean_ctor_get(v_code_1569_, 5);
lean_dec(v_unused_1914_);
v_unused_1915_ = lean_ctor_get(v_code_1569_, 4);
lean_dec(v_unused_1915_);
v_unused_1916_ = lean_ctor_get(v_code_1569_, 3);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v_code_1569_, 2);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1919_);
v___x_1905_ = v_code_1569_;
v_isShared_1906_ = v_isSharedCheck_1913_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v_code_1569_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1913_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 5, v_a_1897_);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_fvarId_1890_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_i_1891_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_offset_1892_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_y_1893_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_ty_1894_);
lean_ctor_set(v_reuseFailAlloc_1912_, 5, v_a_1897_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1908_);
v___x_1910_ = v___x_1899_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v___x_1921_; 
lean_dec(v_a_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_code_1569_);
v___x_1921_ = v___x_1899_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_code_1569_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 6);
return v___x_1896_;
}
}
case 10:
{
lean_object* v_fvarId_1924_; lean_object* v_cidx_1925_; lean_object* v_k_1926_; lean_object* v___x_1927_; 
v_fvarId_1924_ = lean_ctor_get(v_code_1569_, 0);
v_cidx_1925_ = lean_ctor_get(v_code_1569_, 1);
v_k_1926_ = lean_ctor_get(v_code_1569_, 2);
lean_inc_ref(v_k_1926_);
v___x_1927_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1926_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1951_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1951_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1951_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
size_t v___x_1932_; size_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1932_ = lean_ptr_addr(v_k_1926_);
v___x_1933_ = lean_ptr_addr(v_a_1928_);
v___x_1934_ = lean_usize_dec_eq(v___x_1932_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1944_; 
lean_inc(v_cidx_1925_);
lean_inc(v_fvarId_1924_);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; lean_object* v_unused_1946_; lean_object* v_unused_1947_; 
v_unused_1945_ = lean_ctor_get(v_code_1569_, 2);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1947_);
v___x_1936_ = v_code_1569_;
v_isShared_1937_ = v_isSharedCheck_1944_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v_code_1569_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1944_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 2, v_a_1928_);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_fvarId_1924_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_cidx_1925_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_a_1928_);
v___x_1939_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1941_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1939_);
v___x_1941_ = v___x_1930_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec(v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_code_1569_);
v___x_1949_ = v___x_1930_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_code_1569_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 3);
return v___x_1927_;
}
}
case 11:
{
lean_object* v_fvarId_1952_; lean_object* v_n_1953_; uint8_t v_check_1954_; uint8_t v_persistent_1955_; lean_object* v_k_1956_; lean_object* v___x_1957_; 
v_fvarId_1952_ = lean_ctor_get(v_code_1569_, 0);
v_n_1953_ = lean_ctor_get(v_code_1569_, 1);
v_check_1954_ = lean_ctor_get_uint8(v_code_1569_, sizeof(void*)*3);
v_persistent_1955_ = lean_ctor_get_uint8(v_code_1569_, sizeof(void*)*3 + 1);
v_k_1956_ = lean_ctor_get(v_code_1569_, 2);
lean_inc_ref(v_k_1956_);
v___x_1957_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1956_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1981_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1981_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1981_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
size_t v___x_1962_; size_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1962_ = lean_ptr_addr(v_k_1956_);
v___x_1963_ = lean_ptr_addr(v_a_1958_);
v___x_1964_ = lean_usize_dec_eq(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1974_; 
lean_inc(v_n_1953_);
lean_inc(v_fvarId_1952_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1975_ = lean_ctor_get(v_code_1569_, 2);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_1977_);
v___x_1966_ = v_code_1569_;
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v_code_1569_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 2, v_a_1958_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_fvarId_1952_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_n_1953_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_a_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*3, v_check_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*3 + 1, v_persistent_1955_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1969_);
v___x_1971_ = v___x_1960_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v___x_1979_; 
lean_dec(v_a_1958_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v_code_1569_);
v___x_1979_ = v___x_1960_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_code_1569_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 3);
return v___x_1957_;
}
}
case 12:
{
lean_object* v_fvarId_1982_; lean_object* v_n_1983_; uint8_t v_check_1984_; uint8_t v_persistent_1985_; lean_object* v_objs_x3f_1986_; lean_object* v_k_1987_; uint8_t v___x_1988_; 
v_fvarId_1982_ = lean_ctor_get(v_code_1569_, 0);
v_n_1983_ = lean_ctor_get(v_code_1569_, 1);
v_check_1984_ = lean_ctor_get_uint8(v_code_1569_, sizeof(void*)*4);
v_persistent_1985_ = lean_ctor_get_uint8(v_code_1569_, sizeof(void*)*4 + 1);
v_objs_x3f_1986_ = lean_ctor_get(v_code_1569_, 2);
v_k_1987_ = lean_ctor_get(v_code_1569_, 3);
v___x_1988_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1568_, v_fvarId_1982_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_inc_ref(v_k_1987_);
v___x_1989_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_1987_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2014_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2014_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2014_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
size_t v___x_1994_; size_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = lean_ptr_addr(v_k_1987_);
v___x_1995_ = lean_ptr_addr(v_a_1990_);
v___x_1996_ = lean_usize_dec_eq(v___x_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2006_; 
lean_inc(v_objs_x3f_1986_);
lean_inc(v_n_1983_);
lean_inc(v_fvarId_1982_);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2007_ = lean_ctor_get(v_code_1569_, 3);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_code_1569_, 2);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_2010_);
v___x_1998_ = v_code_1569_;
v_isShared_1999_ = v_isSharedCheck_2006_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v_code_1569_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2006_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 3, v_a_1990_);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_fvarId_1982_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_n_1983_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_objs_x3f_1986_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_a_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*4, v_check_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*4 + 1, v_persistent_1985_);
v___x_2001_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2001_);
v___x_2003_ = v___x_1992_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_object* v___x_2012_; 
lean_dec(v_a_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v_code_1569_);
v___x_2012_ = v___x_1992_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_code_1569_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 4);
return v___x_1989_;
}
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
lean_inc_ref(v_k_1987_);
lean_inc(v_n_1983_);
lean_dec_ref_known(v_code_1569_, 4);
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_dec_eq(v_n_1983_, v___x_2015_);
lean_dec(v_n_1983_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_k_1987_);
lean_dec(v_resetTokenId_1568_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_2018_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_2017_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2019_, 0, v_resetTokenId_1568_);
lean_ctor_set(v___x_2019_, 1, v_k_1987_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
}
case 13:
{
lean_object* v_fvarId_2021_; lean_object* v_k_2022_; lean_object* v___x_2023_; 
v_fvarId_2021_ = lean_ctor_get(v_code_1569_, 0);
v_k_2022_ = lean_ctor_get(v_code_1569_, 1);
lean_inc_ref(v_k_2022_);
v___x_2023_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1568_, v_k_2022_, v_origAllocId_1570_, v_isSharedId_1571_, v_currentRetType_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2046_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2046_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2046_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
size_t v___x_2028_; size_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = lean_ptr_addr(v_k_2022_);
v___x_2029_ = lean_ptr_addr(v_a_2024_);
v___x_2030_ = lean_usize_dec_eq(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
lean_inc(v_fvarId_2021_);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_code_1569_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; lean_object* v_unused_2042_; 
v_unused_2041_ = lean_ctor_get(v_code_1569_, 1);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_code_1569_, 0);
lean_dec(v_unused_2042_);
v___x_2032_ = v_code_1569_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v_code_1569_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_2024_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_fvarId_2021_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_a_2024_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2035_);
v___x_2037_ = v___x_2026_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v_a_2024_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_code_1569_);
v___x_2044_ = v___x_2026_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_code_1569_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1569_, 2);
return v___x_2023_;
}
}
default: 
{
lean_object* v___x_2047_; 
lean_dec_ref(v_currentRetType_1572_);
lean_dec(v_isSharedId_1571_);
lean_dec(v_origAllocId_1570_);
lean_dec(v_resetTokenId_1568_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_code_1569_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_2048_, lean_object* v_origAllocId_2049_, lean_object* v_isSharedId_2050_, lean_object* v_resultType_2051_, lean_object* v_x_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2048_, v_x_2052_, v_origAllocId_2049_, v_isSharedId_2050_, v_resultType_2051_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_2059_, lean_object* v_origAllocId_2060_, lean_object* v_isSharedId_2061_, lean_object* v_resultType_2062_, lean_object* v_i_2063_, lean_object* v_as_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_2059_, v_origAllocId_2060_, v_isSharedId_2061_, v_resultType_2062_, v_i_2063_, v_as_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_2071_, lean_object* v_code_2072_, lean_object* v_origAllocId_2073_, lean_object* v_isSharedId_2074_, lean_object* v_currentRetType_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2071_, v_code_2072_, v_origAllocId_2073_, v_isSharedId_2074_, v_currentRetType_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2091_, lean_object* v_ds_2092_, lean_object* v_decl_2093_, lean_object* v_nFields_2094_, lean_object* v_origAllocId_2095_, lean_object* v_k_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2094_, v_origAllocId_2095_, v_ds_2092_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v_fst_2104_; lean_object* v_snd_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2226_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v_fst_2104_ = lean_ctor_get(v_a_2103_, 0);
v_snd_2105_ = lean_ctor_get(v_a_2103_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_a_2103_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2107_ = v_a_2103_;
v_isShared_2108_ = v_isSharedCheck_2226_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_snd_2105_);
lean_inc(v_fst_2104_);
lean_dec(v_a_2103_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2226_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2110_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2109_, v_a_2098_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = 1;
v___x_2113_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2114_ = 0;
v___x_2115_ = l_Lean_Compiler_LCNF_mkParam(v___x_2112_, v_a_2111_, v___x_2113_, v___x_2114_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v_fvarId_2117_; lean_object* v_binderName_2118_; lean_object* v_fvarId_2119_; lean_object* v___x_2120_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v_fvarId_2117_ = lean_ctor_get(v_decl_2093_, 0);
v_binderName_2118_ = lean_ctor_get(v_decl_2093_, 1);
v_fvarId_2119_ = lean_ctor_get(v_a_2116_, 0);
lean_inc_ref(v_currentRetType_2091_);
lean_inc(v_fvarId_2119_);
lean_inc(v_origAllocId_2095_);
lean_inc(v_fvarId_2117_);
v___x_2120_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2117_, v_k_2096_, v_origAllocId_2095_, v_fvarId_2119_, v_currentRetType_2091_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2091_);
v___x_2123_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2121_, v___x_2122_, v_currentRetType_2091_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2209_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2209_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2209_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2118_);
lean_inc(v_fvarId_2117_);
v___x_2129_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2129_, 0, v_fvarId_2117_);
lean_ctor_set(v___x_2129_, 1, v_binderName_2118_);
lean_ctor_set(v___x_2129_, 2, v___x_2128_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*3, v___x_2114_);
v___x_2130_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2131_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2130_, v_a_2098_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = lean_unsigned_to_nat(2u);
v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2135_ = lean_array_push(v___x_2134_, v___x_2129_);
v___x_2136_ = lean_array_push(v___x_2135_, v_a_2116_);
lean_inc_ref(v_currentRetType_2091_);
v___x_2137_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2112_, v_a_2132_, v_currentRetType_2091_, v___x_2136_, v_a_2124_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2140_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2139_, v_a_2098_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc(v_origAllocId_2095_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 15);
lean_ctor_set(v___x_2126_, 0, v_origAllocId_2095_);
v___x_2143_ = v___x_2126_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_origAllocId_2095_);
v___x_2143_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2112_, v_a_2141_, v___x_2113_, v___x_2143_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_fvarId_2146_; lean_object* v_fvarId_2147_; lean_object* v___x_2148_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_fvarId_2146_ = lean_ctor_get(v_a_2138_, 0);
v_fvarId_2147_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_fvarId_2147_);
lean_inc(v_fvarId_2146_);
lean_inc(v_origAllocId_2095_);
v___x_2148_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2095_, v_snd_2105_, v_fvarId_2146_, v_fvarId_2147_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
lean_inc(v_fvarId_2147_);
lean_inc(v_fvarId_2146_);
v___x_2150_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2095_, v_snd_2105_, v_fvarId_2146_, v_fvarId_2147_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_snd_2105_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
lean_inc(v_fvarId_2147_);
v___x_2152_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2147_, v___x_2113_, v_currentRetType_2091_, v_a_2149_, v_a_2151_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v_a_2153_);
lean_ctor_set(v___x_2107_, 0, v_a_2145_);
v___x_2155_ = v___x_2107_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_a_2153_);
v___x_2155_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2112_, v_decl_2093_, v_a_2098_);
lean_dec_ref(v_decl_2093_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2165_; 
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2156_, 0);
lean_dec(v_unused_2166_);
v___x_2158_ = v___x_2156_;
v_isShared_2159_ = v_isSharedCheck_2165_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v___x_2156_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2165_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2160_, 0, v_a_2138_);
lean_ctor_set(v___x_2160_, 1, v___x_2155_);
v___x_2161_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_2104_, v___x_2160_);
lean_dec(v_fst_2104_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2161_);
v___x_2163_ = v___x_2158_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v___x_2155_);
lean_dec(v_a_2138_);
lean_dec(v_fst_2104_);
v_a_2167_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2156_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2156_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
else
{
lean_dec(v_a_2145_);
lean_dec(v_a_2138_);
lean_del_object(v___x_2107_);
lean_dec(v_fst_2104_);
lean_dec_ref(v_decl_2093_);
return v___x_2152_;
}
}
else
{
lean_dec(v_a_2149_);
lean_dec(v_a_2145_);
lean_dec(v_a_2138_);
lean_del_object(v___x_2107_);
lean_dec(v_fst_2104_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
return v___x_2150_;
}
}
else
{
lean_dec(v_a_2145_);
lean_dec(v_a_2138_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
return v___x_2148_;
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2138_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2176_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2144_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2144_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2138_);
lean_del_object(v___x_2126_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2185_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2140_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2140_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_del_object(v___x_2126_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2193_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2137_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2137_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref_known(v___x_2129_, 3);
lean_del_object(v___x_2126_);
lean_dec(v_a_2124_);
lean_dec(v_a_2116_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2201_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2131_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2131_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_dec(v_a_2116_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
return v___x_2123_;
}
}
else
{
lean_dec(v_a_2116_);
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
return v___x_2120_;
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec_ref(v_k_2096_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2210_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2115_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2115_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_del_object(v___x_2107_);
lean_dec(v_snd_2105_);
lean_dec(v_fst_2104_);
lean_dec_ref(v_k_2096_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2218_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2110_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2110_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v_k_2096_);
lean_dec(v_origAllocId_2095_);
lean_dec_ref(v_decl_2093_);
lean_dec_ref(v_currentRetType_2091_);
v_a_2227_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2102_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2102_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2235_, v_x_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2243_, lean_object* v_i_2244_, lean_object* v_as_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_array_get_size(v_as_2245_);
v___x_2252_ = lean_nat_dec_lt(v_i_2244_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_i_2244_);
lean_dec_ref(v_resultType_2243_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_as_2245_);
return v___x_2253_;
}
else
{
lean_object* v___f_2254_; lean_object* v_a_2255_; lean_object* v___x_2256_; 
lean_inc_ref(v_resultType_2243_);
v___f_2254_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2254_, 0, v_resultType_2243_);
v_a_2255_ = lean_array_fget_borrowed(v_as_2245_, v_i_2244_);
lean_inc(v_a_2255_);
v___x_2256_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2255_, v___f_2254_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; size_t v___x_2258_; size_t v___x_2259_; uint8_t v___x_2260_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = lean_ptr_addr(v_a_2255_);
v___x_2259_ = lean_ptr_addr(v_a_2257_);
v___x_2260_ = lean_usize_dec_eq(v___x_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_nat_add(v_i_2244_, v___x_2261_);
v___x_2263_ = lean_array_fset(v_as_2245_, v_i_2244_, v_a_2257_);
lean_dec(v_i_2244_);
v_i_2244_ = v___x_2262_;
v_as_2245_ = v___x_2263_;
goto _start;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec(v_a_2257_);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_add(v_i_2244_, v___x_2265_);
lean_dec(v_i_2244_);
v_i_2244_ = v___x_2266_;
goto _start;
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_as_2245_);
lean_dec(v_i_2244_);
lean_dec_ref(v_resultType_2243_);
v_a_2268_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2256_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2256_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2276_, lean_object* v_ds_2277_, lean_object* v_currentRetType_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_code_2285_; lean_object* v_ds_2286_; lean_object* v_k_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; 
switch(lean_obj_tag(v_code_2276_))
{
case 0:
{
lean_object* v_decl_2296_; lean_object* v_value_2297_; 
v_decl_2296_ = lean_ctor_get(v_code_2276_, 0);
v_value_2297_ = lean_ctor_get(v_decl_2296_, 3);
if (lean_obj_tag(v_value_2297_) == 11)
{
lean_object* v_k_2298_; lean_object* v_n_2299_; lean_object* v_var_2300_; lean_object* v___x_2301_; 
lean_inc_ref(v_decl_2296_);
v_k_2298_ = lean_ctor_get(v_code_2276_, 1);
lean_inc_ref(v_k_2298_);
lean_dec_ref_known(v_code_2276_, 2);
v_n_2299_ = lean_ctor_get(v_value_2297_, 0);
lean_inc(v_n_2299_);
v_var_2300_ = lean_ctor_get(v_value_2297_, 1);
lean_inc(v_var_2300_);
v___x_2301_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2278_, v_ds_2277_, v_decl_2296_, v_n_2299_, v_var_2300_, v_k_2298_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2301_;
}
else
{
lean_object* v_k_2302_; 
v_k_2302_ = lean_ctor_get(v_code_2276_, 1);
lean_inc_ref(v_k_2302_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2302_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
}
case 2:
{
lean_object* v_decl_2303_; lean_object* v_k_2304_; lean_object* v_params_2305_; lean_object* v_type_2306_; lean_object* v_value_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_decl_2303_ = lean_ctor_get(v_code_2276_, 0);
lean_inc_ref(v_decl_2303_);
v_k_2304_ = lean_ctor_get(v_code_2276_, 1);
lean_inc_ref(v_k_2304_);
lean_dec_ref_known(v_code_2276_, 2);
v_params_2305_ = lean_ctor_get(v_decl_2303_, 2);
lean_inc_ref(v_params_2305_);
v_type_2306_ = lean_ctor_get(v_decl_2303_, 3);
lean_inc_ref_n(v_type_2306_, 2);
v_value_2307_ = lean_ctor_get(v_decl_2303_, 4);
v___x_2308_ = 1;
v___x_2309_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2307_);
v___x_2310_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2307_, v___x_2309_, v_type_2306_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2330_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2330_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2330_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2308_, v_decl_2303_, v_type_2306_, v_params_2305_, v_a_2311_, v_a_2280_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
if (v_isShared_2314_ == 0)
{
lean_ctor_set_tag(v___x_2313_, 2);
lean_ctor_set(v___x_2313_, 0, v_a_2316_);
v___x_2318_ = v___x_2313_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2316_);
v___x_2318_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_array_push(v_ds_2277_, v___x_2318_);
v_code_2276_ = v_k_2304_;
v_ds_2277_ = v___x_2319_;
goto _start;
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_del_object(v___x_2313_);
lean_dec_ref(v_k_2304_);
lean_dec_ref(v_currentRetType_2278_);
lean_dec_ref(v_ds_2277_);
v_a_2322_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2315_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2315_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2306_);
lean_dec_ref(v_params_2305_);
lean_dec_ref(v_k_2304_);
lean_dec_ref(v_decl_2303_);
lean_dec_ref(v_currentRetType_2278_);
lean_dec_ref(v_ds_2277_);
return v___x_2310_;
}
}
case 4:
{
lean_object* v_cases_2331_; lean_object* v_typeName_2332_; lean_object* v_resultType_2333_; lean_object* v_discr_2334_; lean_object* v_alts_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_currentRetType_2278_);
v_cases_2331_ = lean_ctor_get(v_code_2276_, 0);
lean_inc_ref(v_cases_2331_);
v_typeName_2332_ = lean_ctor_get(v_cases_2331_, 0);
v_resultType_2333_ = lean_ctor_get(v_cases_2331_, 1);
v_discr_2334_ = lean_ctor_get(v_cases_2331_, 2);
v_alts_2335_ = lean_ctor_get(v_cases_2331_, 3);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_cases_2331_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2337_ = v_cases_2331_;
v_isShared_2338_ = v_isSharedCheck_2374_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_alts_2335_);
lean_inc(v_discr_2334_);
lean_inc(v_resultType_2333_);
lean_inc(v_typeName_2332_);
lean_dec(v_cases_2331_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2374_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2335_);
lean_inc_ref(v_resultType_2333_);
v___x_2340_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2333_, v___x_2339_, v_alts_2335_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2365_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2365_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2365_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___y_2346_; size_t v___x_2351_; size_t v___x_2352_; uint8_t v___x_2353_; 
v___x_2351_ = lean_ptr_addr(v_alts_2335_);
lean_dec_ref(v_alts_2335_);
v___x_2352_ = lean_ptr_addr(v_a_2341_);
v___x_2353_ = lean_usize_dec_eq(v___x_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2363_; 
v_isSharedCheck_2363_ = !lean_is_exclusive(v_code_2276_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_code_2276_, 0);
lean_dec(v_unused_2364_);
v___x_2355_ = v_code_2276_;
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v_code_2276_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 3, v_a_2341_);
v___x_2358_ = v___x_2337_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_typeName_2332_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_resultType_2333_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_discr_2334_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_a_2341_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2358_);
v___x_2360_ = v___x_2355_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
v___y_2346_ = v___x_2360_;
goto v___jp_2345_;
}
}
}
}
else
{
lean_dec(v_a_2341_);
lean_del_object(v___x_2337_);
lean_dec(v_discr_2334_);
lean_dec_ref(v_resultType_2333_);
lean_dec(v_typeName_2332_);
v___y_2346_ = v_code_2276_;
goto v___jp_2345_;
}
v___jp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_ds_2277_, v___y_2346_);
lean_dec_ref(v_ds_2277_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2347_);
v___x_2349_ = v___x_2343_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_del_object(v___x_2337_);
lean_dec_ref(v_alts_2335_);
lean_dec(v_discr_2334_);
lean_dec_ref(v_resultType_2333_);
lean_dec(v_typeName_2332_);
lean_dec_ref_known(v_code_2276_, 1);
lean_dec_ref(v_ds_2277_);
v_a_2366_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2340_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2340_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2375_; 
v_k_2375_ = lean_ctor_get(v_code_2276_, 3);
lean_inc_ref(v_k_2375_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2375_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
case 8:
{
lean_object* v_k_2376_; 
v_k_2376_ = lean_ctor_get(v_code_2276_, 3);
lean_inc_ref(v_k_2376_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2376_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
case 9:
{
lean_object* v_k_2377_; 
v_k_2377_ = lean_ctor_get(v_code_2276_, 5);
lean_inc_ref(v_k_2377_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2377_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
case 10:
{
lean_object* v_k_2378_; 
v_k_2378_ = lean_ctor_get(v_code_2276_, 2);
lean_inc_ref(v_k_2378_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2378_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
case 11:
{
lean_object* v_k_2379_; 
v_k_2379_ = lean_ctor_get(v_code_2276_, 2);
lean_inc_ref(v_k_2379_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2379_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
case 12:
{
lean_object* v_k_2380_; 
v_k_2380_ = lean_ctor_get(v_code_2276_, 3);
lean_inc_ref(v_k_2380_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2380_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
case 13:
{
lean_object* v_k_2381_; 
v_k_2381_ = lean_ctor_get(v_code_2276_, 1);
lean_inc_ref(v_k_2381_);
v_code_2285_ = v_code_2276_;
v_ds_2286_ = v_ds_2277_;
v_k_2287_ = v_k_2381_;
v___y_2288_ = v_a_2279_;
v___y_2289_ = v_a_2280_;
v___y_2290_ = v_a_2281_;
v___y_2291_ = v_a_2282_;
goto v___jp_2284_;
}
default: 
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref(v_currentRetType_2278_);
v___x_2382_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_ds_2277_, v_code_2276_);
lean_dec_ref(v_ds_2277_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
v___jp_2284_:
{
uint8_t v___x_2292_; lean_object* v_d_2293_; lean_object* v___x_2294_; 
v___x_2292_ = 1;
v_d_2293_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2292_, v_code_2285_);
lean_dec_ref(v_code_2285_);
v___x_2294_ = lean_array_push(v_ds_2286_, v_d_2293_);
v_code_2276_ = v_k_2287_;
v_ds_2277_ = v___x_2294_;
v_a_2279_ = v___y_2288_;
v_a_2280_ = v___y_2289_;
v_a_2281_ = v___y_2290_;
v_a_2282_ = v___y_2291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2384_, lean_object* v_x_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2392_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2385_, v___x_2391_, v_resultType_2384_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2393_, lean_object* v_i_2394_, lean_object* v_as_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2393_, v_i_2394_, v_as_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2402_, lean_object* v_ds_2403_, lean_object* v_currentRetType_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2402_, v_ds_2403_, v_currentRetType_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2411_, lean_object* v_ds_2412_, lean_object* v_decl_2413_, lean_object* v_nFields_2414_, lean_object* v_origAllocId_2415_, lean_object* v_k_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2411_, v_ds_2412_, v_decl_2413_, v_nFields_2414_, v_origAllocId_2415_, v_k_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2423_, lean_object* v_v_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
if (lean_obj_tag(v_v_2424_) == 0)
{
lean_object* v_code_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2454_; 
v_code_2430_ = lean_ctor_get(v_v_2424_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_v_2424_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2432_ = v_v_2424_;
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_code_2430_);
lean_dec(v_v_2424_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; 
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2425_);
v___x_2434_ = lean_apply_6(v_f_2423_, v_code_2430_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, lean_box(0));
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2445_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v_a_2435_);
v___x_2440_ = v___x_2432_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2442_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2440_);
v___x_2442_ = v___x_2437_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_del_object(v___x_2432_);
v_a_2446_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2434_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2434_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
else
{
lean_object* v___x_2455_; 
lean_dec_ref(v_f_2423_);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_v_2424_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2456_, lean_object* v_v_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2456_, v_v_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2464_, lean_object* v_f_2465_, lean_object* v_v_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2465_, v_v_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2473_, lean_object* v_f_2474_, lean_object* v_v_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_pu_boxed_2481_; lean_object* v_res_2482_; 
v_pu_boxed_2481_ = lean_unbox(v_pu_2473_);
v_res_2482_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2481_, v_f_2474_, v_v_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_decl_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_toSignature_2490_; lean_object* v_type_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_toSignature_2490_ = lean_ctor_get(v_decl_2483_, 0);
lean_inc_ref(v_toSignature_2490_);
lean_dec_ref(v_decl_2483_);
v_type_2491_ = lean_ctor_get(v_toSignature_2490_, 2);
lean_inc_ref(v_type_2491_);
lean_dec_ref(v_toSignature_2490_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2493_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2484_, v___x_2492_, v_type_2491_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_decl_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_decl_2494_, v_x_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___f_2508_; lean_object* v___x_2509_; 
lean_inc_ref(v_decl_2502_);
v___f_2508_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2508_, 0, v_decl_2502_);
v___x_2509_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2503_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2546_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2546_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2546_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
uint8_t v_resetReuse_2514_; 
v_resetReuse_2514_ = lean_ctor_get_uint8(v_a_2510_, sizeof(void*)*4 + 2);
lean_dec(v_a_2510_);
if (v_resetReuse_2514_ == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref(v___f_2508_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v_decl_2502_);
v___x_2516_ = v___x_2512_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_decl_2502_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
else
{
lean_object* v_toSignature_2518_; lean_object* v_value_2519_; uint8_t v_recursive_2520_; lean_object* v_inlineAttr_x3f_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2545_; 
lean_del_object(v___x_2512_);
v_toSignature_2518_ = lean_ctor_get(v_decl_2502_, 0);
v_value_2519_ = lean_ctor_get(v_decl_2502_, 1);
v_recursive_2520_ = lean_ctor_get_uint8(v_decl_2502_, sizeof(void*)*3);
v_inlineAttr_x3f_2521_ = lean_ctor_get(v_decl_2502_, 2);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_decl_2502_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2523_ = v_decl_2502_;
v_isShared_2524_ = v_isSharedCheck_2545_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_inlineAttr_x3f_2521_);
lean_inc(v_value_2519_);
lean_inc(v_toSignature_2518_);
lean_dec(v_decl_2502_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2545_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2508_, v_value_2519_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2536_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2536_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2536_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v_a_2526_);
v___x_2531_ = v___x_2523_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_toSignature_2518_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_a_2526_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_inlineAttr_x3f_2521_);
lean_ctor_set_uint8(v_reuseFailAlloc_2535_, sizeof(void*)*3, v_recursive_2520_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2533_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2531_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_del_object(v___x_2523_);
lean_dec(v_inlineAttr_x3f_2521_);
lean_dec_ref(v_toSignature_2518_);
v_a_2537_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2525_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2525_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec_ref(v___f_2508_);
lean_dec_ref(v_decl_2502_);
v_a_2547_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2509_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2509_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2561_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2568_ = 2;
v___x_2569_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2570_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2569_, v___x_2568_, v___x_2567_, v___x_2566_);
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2571_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_unsigned_to_nat(2743268278u);
v___x_2628_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2629_ = l_Lean_Name_num___override(v___x_2628_, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2632_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2633_ = l_Lean_Name_str___override(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2636_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2637_ = l_Lean_Name_str___override(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_unsigned_to_nat(2u);
v___x_2639_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2640_ = l_Lean_Name_num___override(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2642_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2643_ = 1;
v___x_2644_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2645_ = l_Lean_registerTraceClass(v___x_2642_, v___x_2643_, v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2647_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_expandResetReuse = _init_l_Lean_Compiler_LCNF_expandResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_expandResetReuse);
res = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
