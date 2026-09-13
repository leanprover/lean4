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
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_2594__overap_43_; lean_object* v___x_44_; 
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
v___x_2594__overap_43_ = lean_panic_fn_borrowed(v___f_42_, v_msg_5_);
lean_dec_ref(v___f_42_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
v___x_44_ = lean_apply_5(v___x_2594__overap_43_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
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
lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_106_; lean_object* v_snd_126_; lean_object* v_fst_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_269_; 
v_snd_126_ = lean_ctor_get(v_a_92_, 1);
v_fst_127_ = lean_ctor_get(v_a_92_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_a_92_);
if (v_isSharedCheck_269_ == 0)
{
v___x_129_ = v_a_92_;
v_isShared_130_ = v_isSharedCheck_269_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_126_);
lean_inc(v_fst_127_);
lean_dec(v_a_92_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_269_;
goto v_resetjp_128_;
}
v___jp_98_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___y_101_);
lean_ctor_set(v___x_102_, 1, v___y_100_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___y_99_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v_a_92_ = v___x_103_;
goto _start;
}
v___jp_105_:
{
if (lean_obj_tag(v___y_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_117_; 
v_a_107_ = lean_ctor_get(v___y_106_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___y_106_);
if (v_isSharedCheck_117_ == 0)
{
v___x_109_ = v___y_106_;
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___y_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
if (lean_obj_tag(v_a_107_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; 
v_a_111_ = lean_ctor_get(v_a_107_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v_a_107_, 1);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v_a_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_object* v_a_115_; 
lean_del_object(v___x_109_);
v_a_115_ = lean_ctor_get(v_a_107_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v_a_107_, 1);
v_a_92_ = v_a_115_;
goto _start;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___y_106_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___y_106_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___y_106_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___y_106_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
v_resetjp_128_:
{
lean_object* v_fst_131_; lean_object* v_snd_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_268_; 
v_fst_131_ = lean_ctor_get(v_snd_126_, 0);
v_snd_132_ = lean_ctor_get(v_snd_126_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v_snd_126_);
if (v_isSharedCheck_268_ == 0)
{
v___x_134_ = v_snd_126_;
v_isShared_135_ = v_isSharedCheck_268_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_snd_132_);
lean_inc(v_fst_131_);
lean_dec(v_snd_126_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_268_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(2u);
v___x_137_ = lean_array_get_size(v_fst_127_);
v___x_138_ = lean_nat_dec_le(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_140_; 
if (v_isShared_135_ == 0)
{
v___x_140_ = v___x_134_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_fst_131_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_snd_132_);
v___x_140_ = v_reuseFailAlloc_145_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_140_);
v___x_142_ = v___x_129_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_fst_127_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_144_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_sub(v___x_137_, v___x_147_);
v___x_149_ = lean_array_get(v___x_146_, v_fst_127_, v___x_148_);
lean_dec(v___x_148_);
switch(lean_obj_tag(v___x_149_))
{
case 0:
{
lean_object* v_decl_150_; lean_object* v_value_151_; 
v_decl_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc_ref(v_decl_150_);
v_value_151_ = lean_ctor_get(v_decl_150_, 3);
lean_inc(v_value_151_);
switch(lean_obj_tag(v_value_151_))
{
case 8:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec_ref_known(v_value_151_, 3);
lean_dec_ref(v_decl_150_);
v___x_152_ = lean_array_pop(v_fst_127_);
v___x_153_ = lean_array_push(v_fst_131_, v___x_149_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_153_);
v___x_155_ = v___x_134_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_snd_132_);
v___x_155_ = v_reuseFailAlloc_160_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_155_);
lean_ctor_set(v___x_129_, 0, v___x_152_);
v___x_157_ = v___x_129_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v_a_92_ = v___x_157_;
goto _start;
}
}
}
case 7:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_dec_ref_known(v_value_151_, 2);
lean_dec_ref(v_decl_150_);
v___x_161_ = lean_array_pop(v_fst_127_);
v___x_162_ = lean_array_push(v_fst_131_, v___x_149_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_162_);
v___x_164_ = v___x_134_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_snd_132_);
v___x_164_ = v_reuseFailAlloc_169_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_164_);
lean_ctor_set(v___x_129_, 0, v___x_161_);
v___x_166_ = v___x_129_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v_a_92_ = v___x_166_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_188_; 
lean_del_object(v___x_134_);
lean_del_object(v___x_129_);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v___x_149_, 0);
lean_dec(v_unused_189_);
v___x_171_ = v___x_149_;
v_isShared_172_ = v_isSharedCheck_188_;
goto v_resetjp_170_;
}
else
{
lean_dec(v___x_149_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_188_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_fvarId_173_; lean_object* v_binderName_174_; lean_object* v_type_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_186_; 
v_fvarId_173_ = lean_ctor_get(v_decl_150_, 0);
v_binderName_174_ = lean_ctor_get(v_decl_150_, 1);
v_type_175_ = lean_ctor_get(v_decl_150_, 2);
v_isSharedCheck_186_ = !lean_is_exclusive(v_decl_150_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v_decl_150_, 3);
lean_dec(v_unused_187_);
v___x_177_ = v_decl_150_;
v_isShared_178_ = v_isSharedCheck_186_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_type_175_);
lean_inc(v_binderName_174_);
lean_inc(v_fvarId_173_);
lean_dec(v_decl_150_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_186_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_fvarId_173_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_binderName_174_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_type_175_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_value_151_);
v___x_180_ = v_reuseFailAlloc_185_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_180_);
v___x_182_ = v___x_171_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_184_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_131_, v_snd_132_, v_fst_127_, v___x_182_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___x_182_);
v___y_106_ = v___x_183_;
goto v___jp_105_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_190_; lean_object* v_n_191_; uint8_t v_check_192_; uint8_t v_persistent_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_fvarId_190_ = lean_ctor_get(v___x_149_, 0);
v_n_191_ = lean_ctor_get(v___x_149_, 1);
v_check_192_ = lean_ctor_get_uint8(v___x_149_, sizeof(void*)*2);
v_persistent_193_ = lean_ctor_get_uint8(v___x_149_, sizeof(void*)*2 + 1);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_nat_dec_lt(v___x_194_, v_n_191_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec_ref_known(v___x_149_, 2);
lean_del_object(v___x_134_);
lean_dec(v_snd_132_);
lean_dec(v_fst_131_);
lean_del_object(v___x_129_);
lean_dec(v_fst_127_);
v___x_196_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
v___x_197_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_196_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
v___y_106_ = v___x_197_;
goto v___jp_105_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_nat_sub(v___x_137_, v___x_136_);
v___x_199_ = lean_array_get(v___x_146_, v_fst_127_, v___x_198_);
lean_dec(v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_decl_200_; lean_object* v_value_201_; 
v_decl_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_decl_200_);
v_value_201_ = lean_ctor_get(v_decl_200_, 3);
lean_inc(v_value_201_);
if (lean_obj_tag(v_value_201_) == 6)
{
lean_object* v_fvarId_202_; lean_object* v_i_203_; lean_object* v_var_204_; lean_object* v___x_205_; uint8_t v___y_207_; uint8_t v___x_244_; 
v_fvarId_202_ = lean_ctor_get(v_decl_200_, 0);
lean_inc(v_fvarId_202_);
lean_dec_ref(v_decl_200_);
v_i_203_ = lean_ctor_get(v_value_201_, 0);
lean_inc(v_i_203_);
v_var_204_ = lean_ctor_get(v_value_201_, 1);
lean_inc(v_var_204_);
lean_dec_ref_known(v_value_201_, 2);
v___x_205_ = lean_box(0);
v___x_244_ = l_Lean_instBEqFVarId_beq(v_fvarId_202_, v_fvarId_190_);
lean_dec(v_fvarId_202_);
if (v___x_244_ == 0)
{
lean_dec(v_var_204_);
v___y_207_ = v___x_244_;
goto v___jp_206_;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = l_Lean_instBEqFVarId_beq(v_targetId_91_, v_var_204_);
lean_dec(v_var_204_);
v___y_207_ = v___x_245_;
goto v___jp_206_;
}
v___jp_206_:
{
if (v___y_207_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v_i_203_);
lean_dec_ref_known(v___x_199_, 1);
lean_dec_ref_known(v___x_149_, 2);
if (v_isShared_135_ == 0)
{
v___x_209_ = v___x_134_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_fst_131_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_snd_132_);
v___x_209_ = v_reuseFailAlloc_214_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_209_);
v___x_211_ = v___x_129_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_fst_127_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_213_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_array_get_borrowed(v___x_205_, v_snd_132_, v_i_203_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_230_; 
lean_inc(v_n_191_);
lean_inc(v_fvarId_190_);
lean_del_object(v___x_134_);
lean_del_object(v___x_129_);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_231_ = lean_ctor_get(v___x_149_, 1);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v___x_149_, 0);
lean_dec(v_unused_232_);
v___x_217_ = v___x_149_;
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
else
{
lean_dec(v___x_149_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_219_ = lean_array_pop(v_fst_127_);
v___x_220_ = lean_array_pop(v___x_219_);
lean_inc(v_fvarId_190_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_fvarId_190_);
v___x_222_ = lean_array_set(v_snd_132_, v_i_203_, v___x_221_);
lean_dec(v_i_203_);
v___x_223_ = lean_array_push(v_fst_131_, v___x_199_);
v___x_224_ = lean_nat_dec_eq(v_n_191_, v___x_147_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_nat_sub(v_n_191_, v___x_147_);
lean_dec(v_n_191_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_225_);
v___x_227_ = v___x_217_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_fvarId_190_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_225_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*2, v_check_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_229_, sizeof(void*)*2 + 1, v_persistent_193_);
v___x_227_ = v_reuseFailAlloc_229_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = lean_array_push(v___x_223_, v___x_227_);
v___y_99_ = v___x_220_;
v___y_100_ = v___x_222_;
v___y_101_ = v___x_228_;
goto v___jp_98_;
}
}
else
{
lean_del_object(v___x_217_);
lean_dec(v_n_191_);
lean_dec(v_fvarId_190_);
v___y_99_ = v___x_220_;
v___y_100_ = v___x_222_;
v___y_101_ = v___x_223_;
goto v___jp_98_;
}
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
lean_dec(v_i_203_);
v___x_233_ = lean_array_push(v_fst_131_, v___x_149_);
v___x_234_ = lean_array_push(v___x_233_, v___x_199_);
v___x_235_ = lean_array_pop(v_fst_127_);
v___x_236_ = lean_array_pop(v___x_235_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_234_);
v___x_238_ = v___x_134_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_snd_132_);
v___x_238_ = v_reuseFailAlloc_243_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_238_);
lean_ctor_set(v___x_129_, 0, v___x_236_);
v___x_240_ = v___x_129_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v_a_92_ = v___x_240_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref_known(v___x_149_, 2);
lean_del_object(v___x_134_);
lean_del_object(v___x_129_);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v___x_199_, 0);
lean_dec(v_unused_265_);
v___x_247_ = v___x_199_;
v_isShared_248_ = v_isSharedCheck_264_;
goto v_resetjp_246_;
}
else
{
lean_dec(v___x_199_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_264_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_fvarId_249_; lean_object* v_binderName_250_; lean_object* v_type_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_262_; 
v_fvarId_249_ = lean_ctor_get(v_decl_200_, 0);
v_binderName_250_ = lean_ctor_get(v_decl_200_, 1);
v_type_251_ = lean_ctor_get(v_decl_200_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_decl_200_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_decl_200_, 3);
lean_dec(v_unused_263_);
v___x_253_ = v_decl_200_;
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_type_251_);
lean_inc(v_binderName_250_);
lean_inc(v_fvarId_249_);
lean_dec(v_decl_200_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_fvarId_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_binderName_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_type_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_value_201_);
v___x_256_ = v_reuseFailAlloc_261_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_256_);
v___x_258_ = v___x_247_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_260_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_131_, v_snd_132_, v_fst_127_, v___x_258_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___x_258_);
v___y_106_ = v___x_259_;
goto v___jp_105_;
}
}
}
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec_ref_known(v___x_149_, 2);
lean_del_object(v___x_134_);
lean_del_object(v___x_129_);
v___x_266_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_131_, v_snd_132_, v_fst_127_, v___x_199_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___x_199_);
v___y_106_ = v___x_266_;
goto v___jp_105_;
}
}
}
default: 
{
lean_object* v___x_267_; 
lean_del_object(v___x_134_);
lean_del_object(v___x_129_);
v___x_267_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_131_, v_snd_132_, v_fst_127_, v___x_149_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___x_149_);
v___y_106_ = v___x_267_;
goto v___jp_105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object* v_targetId_270_, lean_object* v_a_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_270_, v_a_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v_targetId_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_280_, lean_object* v_targetId_281_, lean_object* v_ds_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_keep_288_; lean_object* v___x_289_; lean_object* v_mask_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_keep_288_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_289_ = lean_box(0);
v_mask_290_ = lean_mk_array(v_nFields_280_, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_keep_288_);
lean_ctor_set(v___x_291_, 1, v_mask_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_ds_282_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_281_, v___x_292_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_314_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_314_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_314_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_snd_298_; lean_object* v_fst_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_313_; 
v_snd_298_ = lean_ctor_get(v_a_294_, 1);
lean_inc(v_snd_298_);
v_fst_299_ = lean_ctor_get(v_a_294_, 0);
lean_inc(v_fst_299_);
lean_dec(v_a_294_);
v_fst_300_ = lean_ctor_get(v_snd_298_, 0);
v_snd_301_ = lean_ctor_get(v_snd_298_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_snd_298_);
if (v_isSharedCheck_313_ == 0)
{
v___x_303_ = v_snd_298_;
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snd_301_);
lean_inc(v_fst_300_);
lean_dec(v_snd_298_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = l_Array_reverse___redArg(v_fst_300_);
v___x_306_ = l_Array_append___redArg(v_fst_299_, v___x_305_);
lean_dec_ref(v___x_305_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_snd_301_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_308_);
v___x_310_ = v___x_296_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_293_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_293_);
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
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_323_, lean_object* v_targetId_324_, lean_object* v_ds_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_323_, v_targetId_324_, v_ds_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_targetId_324_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_332_, lean_object* v_inst_333_, lean_object* v_a_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_332_, v_a_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* v_targetId_341_, lean_object* v_inst_342_, lean_object* v_a_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_341_, v_inst_342_, v_a_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v_targetId_341_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_366_, lean_object* v_discrType_367_, lean_object* v_resultType_368_, lean_object* v_t_369_, lean_object* v_e_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_372_ = l_Lean_Expr_getAppFn(v_discrType_367_);
v___x_373_ = l_Lean_Expr_constName_x21(v___x_372_);
lean_dec_ref(v___x_372_);
v___x_374_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_e_370_);
v___x_376_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_t_369_);
v___x_378_ = lean_unsigned_to_nat(2u);
v___x_379_ = lean_mk_empty_array_with_capacity(v___x_378_);
v___x_380_ = lean_array_push(v___x_379_, v___x_375_);
v___x_381_ = lean_array_push(v___x_380_, v___x_377_);
v___x_382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_382_, 0, v___x_373_);
lean_ctor_set(v___x_382_, 1, v_resultType_368_);
lean_ctor_set(v___x_382_, 2, v_discr_366_);
lean_ctor_set(v___x_382_, 3, v___x_381_);
v___x_383_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_385_, lean_object* v_discrType_386_, lean_object* v_resultType_387_, lean_object* v_t_388_, lean_object* v_e_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_385_, v_discrType_386_, v_resultType_387_, v_t_388_, v_e_389_);
lean_dec_ref(v_discrType_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_392_, lean_object* v_discrType_393_, lean_object* v_resultType_394_, lean_object* v_t_395_, lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_392_, v_discrType_393_, v_resultType_394_, v_t_395_, v_e_396_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_403_, lean_object* v_discrType_404_, lean_object* v_resultType_405_, lean_object* v_t_406_, lean_object* v_e_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_403_, v_discrType_404_, v_resultType_405_, v_t_406_, v_e_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_discrType_404_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_416_ = lean_panic_fn_borrowed(v___x_415_, v_msg_414_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_420_ = lean_unsigned_to_nat(11u);
v___x_421_ = lean_unsigned_to_nat(138u);
v___x_422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_423_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_424_ = l_mkPanicMessageWithDecl(v___x_423_, v___x_422_, v___x_421_, v___x_420_, v___x_419_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_bs_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_429_ == 0)
{
lean_dec(v_targetId_425_);
return v_bs_428_;
}
else
{
lean_object* v_v_430_; lean_object* v___x_431_; lean_object* v_bs_x27_432_; lean_object* v___y_434_; 
v_v_430_ = lean_array_uget(v_bs_428_, v_i_427_);
v___x_431_ = lean_unsigned_to_nat(0u);
v_bs_x27_432_ = lean_array_uset(v_bs_428_, v_i_427_, v___x_431_);
switch(lean_obj_tag(v_v_430_))
{
case 3:
{
lean_object* v_i_439_; lean_object* v_y_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_i_439_ = lean_ctor_get(v_v_430_, 1);
v_y_440_ = lean_ctor_get(v_v_430_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_v_430_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_v_430_, 0);
lean_dec(v_unused_448_);
v___x_442_ = v_v_430_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_y_440_);
lean_inc(v_i_439_);
lean_dec(v_v_430_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
lean_inc(v_targetId_425_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v_targetId_425_);
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_targetId_425_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_i_439_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_y_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
v___y_434_ = v___x_445_;
goto v___jp_433_;
}
}
}
case 5:
{
lean_object* v_i_449_; lean_object* v_offset_450_; lean_object* v_y_451_; lean_object* v_ty_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_i_449_ = lean_ctor_get(v_v_430_, 1);
v_offset_450_ = lean_ctor_get(v_v_430_, 2);
v_y_451_ = lean_ctor_get(v_v_430_, 3);
v_ty_452_ = lean_ctor_get(v_v_430_, 4);
v_isSharedCheck_459_ = !lean_is_exclusive(v_v_430_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_v_430_, 0);
lean_dec(v_unused_460_);
v___x_454_ = v_v_430_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_ty_452_);
lean_inc(v_y_451_);
lean_inc(v_offset_450_);
lean_inc(v_i_449_);
lean_dec(v_v_430_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
lean_inc(v_targetId_425_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_targetId_425_);
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_targetId_425_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_i_449_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_offset_450_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_y_451_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_ty_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
v___y_434_ = v___x_457_;
goto v___jp_433_;
}
}
}
case 4:
{
lean_object* v_i_461_; lean_object* v_y_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_i_461_ = lean_ctor_get(v_v_430_, 1);
v_y_462_ = lean_ctor_get(v_v_430_, 2);
v_isSharedCheck_469_ = !lean_is_exclusive(v_v_430_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_v_430_, 0);
lean_dec(v_unused_470_);
v___x_464_ = v_v_430_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_y_462_);
lean_inc(v_i_461_);
lean_dec(v_v_430_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
lean_inc(v_targetId_425_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v_targetId_425_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_targetId_425_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_i_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_y_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v___y_434_ = v___x_467_;
goto v___jp_433_;
}
}
}
default: 
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_v_430_);
v___x_471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_472_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_471_);
v___y_434_ = v___x_472_;
goto v___jp_433_;
}
}
v___jp_433_:
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_427_, v___x_435_);
v___x_437_ = lean_array_uset(v_bs_x27_432_, v_i_427_, v___y_434_);
v_i_427_ = v___x_436_;
v_bs_428_ = v___x_437_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_473_, lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_bs_476_){
_start:
{
size_t v_sz_boxed_477_; size_t v_i_boxed_478_; lean_object* v_res_479_; 
v_sz_boxed_477_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_478_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_473_, v_sz_boxed_477_, v_i_boxed_478_, v_bs_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_480_, lean_object* v_sets_481_){
_start:
{
size_t v_sz_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_sz_483_ = lean_array_size(v_sets_481_);
v___x_484_ = ((size_t)0ULL);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_480_, v_sz_483_, v___x_484_, v_sets_481_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_487_, lean_object* v_sets_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_487_, v_sets_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_491_, lean_object* v_sets_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_491_, v_sets_492_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_499_, lean_object* v_sets_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_499_, v_sets_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_507_, lean_object* v_i_508_, lean_object* v_y_509_, lean_object* v_a_510_){
_start:
{
if (lean_obj_tag(v_y_509_) == 0)
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = 0;
v___x_513_ = lean_box(v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_fvarId_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
v_fvarId_515_ = lean_ctor_get(v_y_509_, 0);
v___x_516_ = 1;
v___x_517_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_516_, v_fvarId_515_, v_a_510_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_545_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_545_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_545_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_545_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
if (lean_obj_tag(v_a_518_) == 1)
{
lean_object* v_val_522_; 
v_val_522_ = lean_ctor_get(v_a_518_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_a_518_, 1);
if (lean_obj_tag(v_val_522_) == 6)
{
lean_object* v_i_523_; lean_object* v_var_524_; uint8_t v___x_525_; 
v_i_523_ = lean_ctor_get(v_val_522_, 0);
lean_inc(v_i_523_);
v_var_524_ = lean_ctor_get(v_val_522_, 1);
lean_inc(v_var_524_);
lean_dec_ref_known(v_val_522_, 2);
v___x_525_ = lean_nat_dec_eq(v_i_508_, v_i_523_);
lean_dec(v_i_523_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_528_; 
lean_dec(v_var_524_);
v___x_526_ = lean_box(v___x_525_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_526_);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_530_ = l_Lean_instBEqFVarId_beq(v_fvarId_507_, v_var_524_);
lean_dec(v_var_524_);
v___x_531_ = lean_box(v___x_530_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_531_);
v___x_533_ = v___x_520_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
else
{
uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
lean_dec(v_val_522_);
v___x_535_ = 0;
v___x_536_ = lean_box(v___x_535_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_536_);
v___x_538_ = v___x_520_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
lean_dec(v_a_518_);
v___x_540_ = 0;
v___x_541_ = lean_box(v___x_540_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_541_);
v___x_543_ = v___x_520_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_517_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_517_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_554_, lean_object* v_i_555_, lean_object* v_y_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_554_, v_i_555_, v_y_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec(v_y_556_);
lean_dec(v_i_555_);
lean_dec(v_fvarId_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_560_, lean_object* v_i_561_, lean_object* v_y_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_560_, v_i_561_, v_y_562_, v_a_564_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_569_, lean_object* v_i_570_, lean_object* v_y_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_569_, v_i_570_, v_y_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_y_571_);
lean_dec(v_i_570_);
lean_dec(v_fvarId_569_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_578_, lean_object* v_i_579_, lean_object* v_y_580_, lean_object* v_a_581_){
_start:
{
uint8_t v___x_583_; lean_object* v___x_584_; 
v___x_583_ = 1;
v___x_584_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_583_, v_y_580_, v_a_581_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_612_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_612_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_612_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_612_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
if (lean_obj_tag(v_a_585_) == 1)
{
lean_object* v_val_589_; 
v_val_589_ = lean_ctor_get(v_a_585_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_a_585_, 1);
if (lean_obj_tag(v_val_589_) == 7)
{
lean_object* v_i_590_; lean_object* v_var_591_; uint8_t v___x_592_; 
v_i_590_ = lean_ctor_get(v_val_589_, 0);
lean_inc(v_i_590_);
v_var_591_ = lean_ctor_get(v_val_589_, 1);
lean_inc(v_var_591_);
lean_dec_ref_known(v_val_589_, 2);
v___x_592_ = lean_nat_dec_eq(v_i_579_, v_i_590_);
lean_dec(v_i_590_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_dec(v_var_591_);
v___x_593_ = lean_box(v___x_592_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_593_);
v___x_595_ = v___x_587_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
else
{
uint8_t v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_597_ = l_Lean_instBEqFVarId_beq(v_fvarId_578_, v_var_591_);
lean_dec(v_var_591_);
v___x_598_ = lean_box(v___x_597_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_598_);
v___x_600_ = v___x_587_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
lean_dec(v_val_589_);
v___x_602_ = 0;
v___x_603_ = lean_box(v___x_602_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_603_);
v___x_605_ = v___x_587_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
lean_dec(v_a_585_);
v___x_607_ = 0;
v___x_608_ = lean_box(v___x_607_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_608_);
v___x_610_ = v___x_587_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_a_613_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_584_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_584_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_621_, lean_object* v_i_622_, lean_object* v_y_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_621_, v_i_622_, v_y_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec(v_y_623_);
lean_dec(v_i_622_);
lean_dec(v_fvarId_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_627_, lean_object* v_i_628_, lean_object* v_y_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_627_, v_i_628_, v_y_629_, v_a_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_636_, lean_object* v_i_637_, lean_object* v_y_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_636_, v_i_637_, v_y_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_y_638_);
lean_dec(v_i_637_);
lean_dec(v_fvarId_636_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_645_, lean_object* v_i_646_, lean_object* v_offset_647_, lean_object* v_y_648_, lean_object* v_a_649_){
_start:
{
uint8_t v___x_651_; lean_object* v___x_652_; 
v___x_651_ = 1;
v___x_652_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_651_, v_y_648_, v_a_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_686_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_686_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_686_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_686_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
if (lean_obj_tag(v_a_653_) == 1)
{
lean_object* v_val_657_; 
v_val_657_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_a_653_, 1);
if (lean_obj_tag(v_val_657_) == 8)
{
lean_object* v_n_658_; lean_object* v_offset_659_; lean_object* v_var_660_; uint8_t v___x_661_; 
v_n_658_ = lean_ctor_get(v_val_657_, 0);
lean_inc(v_n_658_);
v_offset_659_ = lean_ctor_get(v_val_657_, 1);
lean_inc(v_offset_659_);
v_var_660_ = lean_ctor_get(v_val_657_, 2);
lean_inc(v_var_660_);
lean_dec_ref_known(v_val_657_, 3);
v___x_661_ = lean_nat_dec_eq(v_i_646_, v_n_658_);
lean_dec(v_n_658_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec(v_var_660_);
lean_dec(v_offset_659_);
v___x_662_ = lean_box(v___x_661_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_662_);
v___x_664_ = v___x_655_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
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
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_eq(v_offset_647_, v_offset_659_);
lean_dec(v_offset_659_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec(v_var_660_);
v___x_667_ = lean_box(v___x_666_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_667_);
v___x_669_ = v___x_655_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = l_Lean_instBEqFVarId_beq(v_fvarId_645_, v_var_660_);
lean_dec(v_var_660_);
v___x_672_ = lean_box(v___x_671_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_672_);
v___x_674_ = v___x_655_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec(v_val_657_);
v___x_676_ = 0;
v___x_677_ = lean_box(v___x_676_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_677_);
v___x_679_ = v___x_655_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec(v_a_653_);
v___x_681_ = 0;
v___x_682_ = lean_box(v___x_681_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_682_);
v___x_684_ = v___x_655_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_a_687_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_652_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_652_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_695_, lean_object* v_i_696_, lean_object* v_offset_697_, lean_object* v_y_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_695_, v_i_696_, v_offset_697_, v_y_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec(v_y_698_);
lean_dec(v_offset_697_);
lean_dec(v_i_696_);
lean_dec(v_fvarId_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_702_, lean_object* v_i_703_, lean_object* v_offset_704_, lean_object* v_y_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_702_, v_i_703_, v_offset_704_, v_y_705_, v_a_707_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_712_, lean_object* v_i_713_, lean_object* v_offset_714_, lean_object* v_y_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_712_, v_i_713_, v_offset_714_, v_y_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_y_715_);
lean_dec(v_offset_714_);
lean_dec(v_i_713_);
lean_dec(v_fvarId_712_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_toApplicative_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_764_; 
v___x_728_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_729_ = l_StateRefT_x27_instMonad___redArg(v___x_728_);
v_toApplicative_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v___x_729_, 1);
lean_dec(v_unused_765_);
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_764_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_toApplicative_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_764_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_toFunctor_734_; lean_object* v_toSeq_735_; lean_object* v_toSeqLeft_736_; lean_object* v_toSeqRight_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_762_; 
v_toFunctor_734_ = lean_ctor_get(v_toApplicative_730_, 0);
v_toSeq_735_ = lean_ctor_get(v_toApplicative_730_, 2);
v_toSeqLeft_736_ = lean_ctor_get(v_toApplicative_730_, 3);
v_toSeqRight_737_ = lean_ctor_get(v_toApplicative_730_, 4);
v_isSharedCheck_762_ = !lean_is_exclusive(v_toApplicative_730_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_toApplicative_730_, 1);
lean_dec(v_unused_763_);
v___x_739_ = v_toApplicative_730_;
v_isShared_740_ = v_isSharedCheck_762_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_toSeqRight_737_);
lean_inc(v_toSeqLeft_736_);
lean_inc(v_toSeq_735_);
lean_inc(v_toFunctor_734_);
lean_dec(v_toApplicative_730_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_762_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___x_750_; 
v___f_741_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_742_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_734_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_743_, 0, v_toFunctor_734_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_744_, 0, v_toFunctor_734_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___f_743_);
lean_ctor_set(v___x_745_, 1, v___f_744_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_746_, 0, v_toSeqRight_737_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_747_, 0, v_toSeqLeft_736_);
v___f_748_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_748_, 0, v_toSeq_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v___f_746_);
lean_ctor_set(v___x_739_, 3, v___f_747_);
lean_ctor_set(v___x_739_, 2, v___f_748_);
lean_ctor_set(v___x_739_, 1, v___f_741_);
lean_ctor_set(v___x_739_, 0, v___x_745_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___f_741_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v___f_748_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v___f_747_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v___f_746_);
v___x_750_ = v_reuseFailAlloc_761_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___f_742_);
lean_ctor_set(v___x_732_, 0, v___x_750_);
v___x_752_ = v___x_732_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___f_742_);
v___x_752_ = v_reuseFailAlloc_760_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___f_757_; lean_object* v___x_883__overap_758_; lean_object* v___x_759_; 
v___x_753_ = l_StateRefT_x27_instMonad___redArg(v___x_752_);
v___x_754_ = 0;
v___x_755_ = lean_box(v___x_754_);
v___x_756_ = l_instInhabitedOfMonad___redArg(v___x_753_, v___x_755_);
v___f_757_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_757_, 0, v___x_756_);
v___x_883__overap_758_ = lean_panic_fn_borrowed(v___f_757_, v_msg_722_);
lean_dec_ref(v___f_757_);
lean_inc(v___y_726_);
lean_inc_ref(v___y_725_);
lean_inc(v___y_724_);
lean_inc_ref(v___y_723_);
v___x_759_ = lean_apply_5(v___x_883__overap_758_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, lean_box(0));
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_772_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_775_ = lean_unsigned_to_nat(13u);
v___x_776_ = lean_unsigned_to_nat(174u);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_778_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_779_ = l_mkPanicMessageWithDecl(v___x_778_, v___x_777_, v___x_776_, v___x_775_, v___x_774_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_780_, lean_object* v_as_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_a_791_; uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_b_784_);
return v___x_796_;
}
else
{
lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_835_; 
v_fst_797_ = lean_ctor_get(v_b_784_, 0);
v_snd_798_ = lean_ctor_get(v_b_784_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_b_784_);
if (v_isSharedCheck_835_ == 0)
{
v___x_800_ = v_b_784_;
v_isShared_801_ = v_isSharedCheck_835_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_inc(v_fst_797_);
lean_dec(v_b_784_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_835_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_a_802_; lean_object* v___y_804_; 
v_a_802_ = lean_array_uget_borrowed(v_as_781_, v_i_783_);
switch(lean_obj_tag(v_a_802_))
{
case 3:
{
lean_object* v_i_823_; lean_object* v_y_824_; lean_object* v___x_825_; 
v_i_823_ = lean_ctor_get(v_a_802_, 1);
v_y_824_ = lean_ctor_get(v_a_802_, 2);
v___x_825_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_780_, v_i_823_, v_y_824_, v___y_786_);
v___y_804_ = v___x_825_;
goto v___jp_803_;
}
case 4:
{
lean_object* v_i_826_; lean_object* v_y_827_; lean_object* v___x_828_; 
v_i_826_ = lean_ctor_get(v_a_802_, 1);
v_y_827_ = lean_ctor_get(v_a_802_, 2);
v___x_828_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_780_, v_i_826_, v_y_827_, v___y_786_);
v___y_804_ = v___x_828_;
goto v___jp_803_;
}
case 5:
{
lean_object* v_i_829_; lean_object* v_offset_830_; lean_object* v_y_831_; lean_object* v___x_832_; 
v_i_829_ = lean_ctor_get(v_a_802_, 1);
v_offset_830_ = lean_ctor_get(v_a_802_, 2);
v_y_831_ = lean_ctor_get(v_a_802_, 3);
v___x_832_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_780_, v_i_829_, v_offset_830_, v_y_831_, v___y_786_);
v___y_804_ = v___x_832_;
goto v___jp_803_;
}
default: 
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_834_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_833_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
v___y_804_ = v___x_834_;
goto v___jp_803_;
}
}
v___jp_803_:
{
if (lean_obj_tag(v___y_804_) == 0)
{
lean_object* v_a_805_; uint8_t v___x_806_; 
v_a_805_ = lean_ctor_get(v___y_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___y_804_, 1);
v___x_806_ = lean_unbox(v_a_805_);
lean_dec(v_a_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_inc(v_a_802_);
v___x_807_ = lean_array_push(v_fst_797_, v_a_802_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_807_);
v___x_809_ = v___x_800_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_snd_798_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v_a_791_ = v___x_809_;
goto v___jp_790_;
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_a_802_);
v___x_811_ = lean_array_push(v_snd_798_, v_a_802_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_811_);
v___x_813_ = v___x_800_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_fst_797_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
v_a_791_ = v___x_813_;
goto v___jp_790_;
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_800_);
lean_dec(v_snd_798_);
lean_dec(v_fst_797_);
v_a_815_ = lean_ctor_get(v___y_804_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___y_804_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___y_804_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___y_804_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
v___jp_790_:
{
size_t v___x_792_; size_t v___x_793_; 
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_i_783_, v___x_792_);
v_i_783_ = v___x_793_;
v_b_784_ = v_a_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_836_, lean_object* v_as_837_, lean_object* v_sz_838_, lean_object* v_i_839_, lean_object* v_b_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
size_t v_sz_boxed_846_; size_t v_i_boxed_847_; lean_object* v_res_848_; 
v_sz_boxed_846_ = lean_unbox_usize(v_sz_838_);
lean_dec(v_sz_838_);
v_i_boxed_847_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_836_, v_as_837_, v_sz_boxed_846_, v_i_boxed_847_, v_b_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v_as_837_);
lean_dec(v_selfId_836_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_851_, lean_object* v_sets_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; size_t v_sz_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_859_ = lean_array_size(v_sets_852_);
v___x_860_ = ((size_t)0ULL);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_851_, v_sets_852_, v_sz_859_, v___x_860_, v___x_858_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_878_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_878_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_878_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_878_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_877_; 
v_fst_866_ = lean_ctor_get(v_a_862_, 0);
v_snd_867_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_877_ == 0)
{
v___x_869_ = v_a_862_;
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_snd_867_);
lean_inc(v_fst_866_);
lean_dec(v_a_862_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v_fst_866_);
lean_ctor_set(v___x_869_, 0, v_snd_867_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_snd_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_fst_866_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_872_);
v___x_874_ = v___x_864_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
else
{
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_879_, lean_object* v_sets_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_879_, v_sets_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec_ref(v_sets_880_);
lean_dec(v_selfId_879_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_snd_890_; 
v_snd_890_ = lean_ctor_get(v_a_888_, 1);
lean_inc(v_snd_890_);
switch(lean_obj_tag(v_snd_890_))
{
case 7:
{
lean_object* v_fst_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_909_; 
v_fst_891_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_a_888_, 1);
lean_dec(v_unused_910_);
v___x_893_ = v_a_888_;
v_isShared_894_ = v_isSharedCheck_909_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_fst_891_);
lean_dec(v_a_888_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_909_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_fvarId_895_; lean_object* v_k_896_; uint8_t v___x_897_; 
v_fvarId_895_ = lean_ctor_get(v_snd_890_, 0);
v_k_896_ = lean_ctor_get(v_snd_890_, 3);
v___x_897_ = l_Lean_instBEqFVarId_beq(v_target_887_, v_fvarId_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_899_; 
if (v_isShared_894_ == 0)
{
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_fst_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_snd_890_);
v___x_899_ = v_reuseFailAlloc_901_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
else
{
uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_inc_ref(v_k_896_);
v___x_902_ = 1;
v___x_903_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_902_, v_snd_890_);
lean_dec_ref_known(v_snd_890_, 4);
v___x_904_ = lean_array_push(v_fst_891_, v___x_903_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_k_896_);
lean_ctor_set(v___x_893_, 0, v___x_904_);
v___x_906_ = v___x_893_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_k_896_);
v___x_906_ = v_reuseFailAlloc_908_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v_a_888_ = v___x_906_;
goto _start;
}
}
}
}
case 9:
{
lean_object* v_fst_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_929_; 
v_fst_911_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v_a_888_, 1);
lean_dec(v_unused_930_);
v___x_913_ = v_a_888_;
v_isShared_914_ = v_isSharedCheck_929_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_fst_911_);
lean_dec(v_a_888_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_929_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_fvarId_915_; lean_object* v_k_916_; uint8_t v___x_917_; 
v_fvarId_915_ = lean_ctor_get(v_snd_890_, 0);
v_k_916_ = lean_ctor_get(v_snd_890_, 5);
v___x_917_ = l_Lean_instBEqFVarId_beq(v_target_887_, v_fvarId_915_);
if (v___x_917_ == 0)
{
lean_object* v___x_919_; 
if (v_isShared_914_ == 0)
{
v___x_919_ = v___x_913_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_fst_911_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_snd_890_);
v___x_919_ = v_reuseFailAlloc_921_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
else
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
lean_inc_ref(v_k_916_);
v___x_922_ = 1;
v___x_923_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_922_, v_snd_890_);
lean_dec_ref_known(v_snd_890_, 6);
v___x_924_ = lean_array_push(v_fst_911_, v___x_923_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v_k_916_);
lean_ctor_set(v___x_913_, 0, v___x_924_);
v___x_926_ = v___x_913_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_k_916_);
v___x_926_ = v_reuseFailAlloc_928_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v_a_888_ = v___x_926_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_fst_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_949_; 
v_fst_931_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_a_888_, 1);
lean_dec(v_unused_950_);
v___x_933_ = v_a_888_;
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_fst_931_);
lean_dec(v_a_888_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_949_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_fvarId_935_; lean_object* v_k_936_; uint8_t v___x_937_; 
v_fvarId_935_ = lean_ctor_get(v_snd_890_, 0);
v_k_936_ = lean_ctor_get(v_snd_890_, 3);
v___x_937_ = l_Lean_instBEqFVarId_beq(v_target_887_, v_fvarId_935_);
if (v___x_937_ == 0)
{
lean_object* v___x_939_; 
if (v_isShared_934_ == 0)
{
v___x_939_ = v___x_933_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_fst_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_snd_890_);
v___x_939_ = v_reuseFailAlloc_941_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
else
{
uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
lean_inc_ref(v_k_936_);
v___x_942_ = 1;
v___x_943_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_942_, v_snd_890_);
lean_dec_ref_known(v_snd_890_, 4);
v___x_944_ = lean_array_push(v_fst_931_, v___x_943_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_k_936_);
lean_ctor_set(v___x_933_, 0, v___x_944_);
v___x_946_ = v___x_933_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_936_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
v_a_888_ = v___x_946_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_fst_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
v_fst_951_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_a_888_, 1);
lean_dec(v_unused_960_);
v___x_953_ = v_a_888_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_fst_951_);
lean_dec(v_a_888_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_fst_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_snd_890_);
v___x_956_ = v_reuseFailAlloc_958_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_961_, lean_object* v_a_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_961_, v_a_962_);
lean_dec(v_target_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_965_, lean_object* v_k_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_sets_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_sets_972_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_sets_972_);
lean_ctor_set(v___x_973_, 1, v_k_966_);
v___x_974_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_965_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_991_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_991_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_991_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_990_; 
v_fst_979_ = lean_ctor_get(v_a_975_, 0);
v_snd_980_ = lean_ctor_get(v_a_975_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_a_975_);
if (v_isSharedCheck_990_ == 0)
{
v___x_982_ = v_a_975_;
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snd_980_);
lean_inc(v_fst_979_);
lean_dec(v_a_975_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_fst_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_snd_980_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
else
{
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_992_, lean_object* v_k_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_992_, v_k_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_target_992_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_1000_, lean_object* v_inst_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_1000_, v_a_1002_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_1009_, lean_object* v_inst_1010_, lean_object* v_a_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1009_, v_inst_1010_, v_a_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v_target_1009_);
return v_res_1017_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_1026_ = l_Lean_Expr_const___override(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1027_, lean_object* v_mask_1028_, lean_object* v_origAllocId_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_a_1038_; uint8_t v___x_1042_; 
v___x_1042_ = lean_nat_dec_lt(v_a_1030_, v_upperBound_1027_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_dec(v_a_1030_);
lean_dec(v_origAllocId_1029_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_b_1031_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_array_fget_borrowed(v_mask_1028_, v_a_1030_);
if (lean_obj_tag(v___x_1044_) == 0)
{
uint8_t v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = 1;
v___x_1046_ = 0;
v___x_1047_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_1048_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1047_, v___y_1033_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_1029_);
lean_inc(v_a_1030_);
v___x_1051_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_a_1030_);
lean_ctor_set(v___x_1051_, 1, v_origAllocId_1029_);
v___x_1052_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1045_, v_a_1049_, v___x_1050_, v___x_1051_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_fvarId_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v_fvarId_1054_ = lean_ctor_get(v_a_1053_, 0);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_box(0);
lean_inc(v_fvarId_1054_);
v___x_1057_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v___x_1057_, 0, v_fvarId_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
lean_ctor_set(v___x_1057_, 2, v___x_1056_);
lean_ctor_set(v___x_1057_, 3, v_b_1031_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*4, v___x_1042_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*4 + 1, v___x_1046_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v_a_1053_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v_a_1038_ = v___x_1058_;
goto v___jp_1037_;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_b_1031_);
lean_dec(v_a_1030_);
lean_dec(v_origAllocId_1029_);
v_a_1059_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1052_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1052_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v_b_1031_);
lean_dec(v_a_1030_);
lean_dec(v_origAllocId_1029_);
v_a_1067_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1048_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1048_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
v_a_1038_ = v_b_1031_;
goto v___jp_1037_;
}
}
v___jp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_a_1030_, v___x_1039_);
lean_dec(v_a_1030_);
v_a_1030_ = v___x_1040_;
v_b_1031_ = v_a_1038_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1075_, lean_object* v_mask_1076_, lean_object* v_origAllocId_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1075_, v_mask_1076_, v_origAllocId_1077_, v_a_1078_, v_b_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v_mask_1076_);
lean_dec(v_upperBound_1075_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1086_, lean_object* v_mask_1087_, lean_object* v_resetJpId_1088_, lean_object* v_isSharedId_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v_code_1103_; lean_object* v___x_1104_; 
lean_inc(v_origAllocId_1086_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_origAllocId_1086_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_isSharedId_1089_);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_array_get_size(v_mask_1087_);
v___x_1099_ = lean_unsigned_to_nat(2u);
v___x_1100_ = lean_mk_empty_array_with_capacity(v___x_1099_);
v___x_1101_ = lean_array_push(v___x_1100_, v___x_1095_);
v___x_1102_ = lean_array_push(v___x_1101_, v___x_1096_);
v_code_1103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1103_, 0, v_resetJpId_1088_);
lean_ctor_set(v_code_1103_, 1, v___x_1102_);
v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1098_, v_mask_1087_, v_origAllocId_1086_, v___x_1097_, v_code_1103_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1105_, lean_object* v_mask_1106_, lean_object* v_resetJpId_1107_, lean_object* v_isSharedId_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1105_, v_mask_1106_, v_resetJpId_1107_, v_isSharedId_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec_ref(v_mask_1106_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1115_, lean_object* v_mask_1116_, lean_object* v_origAllocId_1117_, lean_object* v_inst_1118_, lean_object* v_R_1119_, lean_object* v_a_1120_, lean_object* v_b_1121_, lean_object* v_c_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1115_, v_mask_1116_, v_origAllocId_1117_, v_a_1120_, v_b_1121_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1129_, lean_object* v_mask_1130_, lean_object* v_origAllocId_1131_, lean_object* v_inst_1132_, lean_object* v_R_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v_c_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1129_, v_mask_1130_, v_origAllocId_1131_, v_inst_1132_, v_R_1133_, v_a_1134_, v_b_1135_, v_c_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec_ref(v_mask_1130_);
lean_dec(v_upperBound_1129_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1143_, size_t v_sz_1144_, size_t v_i_1145_, lean_object* v_b_1146_){
_start:
{
lean_object* v_a_1149_; uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_lt(v_i_1145_, v_sz_1144_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_b_1146_);
return v___x_1154_;
}
else
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_array_uget_borrowed(v_as_1143_, v_i_1145_);
if (lean_obj_tag(v_a_1155_) == 1)
{
lean_object* v_val_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; 
v_val_1156_ = lean_ctor_get(v_a_1155_, 0);
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = 0;
lean_inc(v_val_1156_);
v___x_1159_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1159_, 0, v_val_1156_);
lean_ctor_set(v___x_1159_, 1, v___x_1157_);
lean_ctor_set(v___x_1159_, 2, v_b_1146_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*3, v___x_1153_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*3 + 1, v___x_1158_);
v_a_1149_ = v___x_1159_;
goto v___jp_1148_;
}
else
{
v_a_1149_ = v_b_1146_;
goto v___jp_1148_;
}
}
v___jp_1148_:
{
size_t v___x_1150_; size_t v___x_1151_; 
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1145_, v___x_1150_);
v_i_1145_ = v___x_1151_;
v_b_1146_ = v_a_1149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1160_, lean_object* v_sz_1161_, lean_object* v_i_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_){
_start:
{
size_t v_sz_boxed_1165_; size_t v_i_boxed_1166_; lean_object* v_res_1167_; 
v_sz_boxed_1165_ = lean_unbox_usize(v_sz_1161_);
lean_dec(v_sz_1161_);
v_i_boxed_1166_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1160_, v_sz_boxed_1165_, v_i_boxed_1166_, v_b_1163_);
lean_dec_ref(v_as_1160_);
return v_res_1167_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_unsigned_to_nat(2u);
v___x_1170_ = lean_mk_empty_array_with_capacity(v___x_1169_);
v___x_1171_ = lean_array_push(v___x_1170_, v___x_1168_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1172_, lean_object* v_mask_1173_, lean_object* v_resetJpId_1174_, lean_object* v_isSharedId_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_code_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v_code_1189_; size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_isSharedId_1175_);
v___x_1182_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1183_ = lean_array_push(v___x_1182_, v___x_1181_);
v_code_1184_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1184_, 0, v_resetJpId_1174_);
lean_ctor_set(v_code_1184_, 1, v___x_1183_);
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = 1;
v___x_1187_ = 0;
v___x_1188_ = lean_box(0);
v_code_1189_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_code_1189_, 0, v_origAllocId_1172_);
lean_ctor_set(v_code_1189_, 1, v___x_1185_);
lean_ctor_set(v_code_1189_, 2, v___x_1188_);
lean_ctor_set(v_code_1189_, 3, v_code_1184_);
lean_ctor_set_uint8(v_code_1189_, sizeof(void*)*4, v___x_1186_);
lean_ctor_set_uint8(v_code_1189_, sizeof(void*)*4 + 1, v___x_1187_);
v_sz_1190_ = lean_array_size(v_mask_1173_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1173_, v_sz_1190_, v___x_1191_, v_code_1189_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___boxed(lean_object* v_origAllocId_1193_, lean_object* v_mask_1194_, lean_object* v_resetJpId_1195_, lean_object* v_isSharedId_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_1193_, v_mask_1194_, v_resetJpId_1195_, v_isSharedId_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec_ref(v_mask_1194_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(lean_object* v_as_1203_, size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_b_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1203_, v_sz_1204_, v_i_1205_, v_b_1206_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___boxed(lean_object* v_as_1213_, lean_object* v_sz_1214_, lean_object* v_i_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
size_t v_sz_boxed_1222_; size_t v_i_boxed_1223_; lean_object* v_res_1224_; 
v_sz_boxed_1222_ = lean_unbox_usize(v_sz_1214_);
lean_dec(v_sz_1214_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0(v_as_1213_, v_sz_boxed_1222_, v_i_boxed_1223_, v_b_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_as_1213_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1225_, lean_object* v_args_1226_, lean_object* v_origAllocId_1227_, lean_object* v_resetTokenId_1228_, lean_object* v_a_1229_, lean_object* v_b_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_a_1234_; uint8_t v___x_1238_; 
v___x_1238_ = lean_nat_dec_lt(v_a_1229_, v_upperBound_1225_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec(v_a_1229_);
lean_dec(v_resetTokenId_1228_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_b_1230_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_array_fget_borrowed(v_args_1226_, v_a_1229_);
v___x_1241_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1227_, v_a_1229_, v___x_1240_, v___y_1231_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_inc(v___x_1240_);
lean_inc(v_a_1229_);
lean_inc(v_resetTokenId_1228_);
v___x_1244_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1244_, 0, v_resetTokenId_1228_);
lean_ctor_set(v___x_1244_, 1, v_a_1229_);
lean_ctor_set(v___x_1244_, 2, v___x_1240_);
lean_ctor_set(v___x_1244_, 3, v_b_1230_);
v_a_1234_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
v_a_1234_ = v_b_1230_;
goto v___jp_1233_;
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_b_1230_);
lean_dec(v_a_1229_);
lean_dec(v_resetTokenId_1228_);
v_a_1245_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1241_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1241_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_nat_add(v_a_1229_, v___x_1235_);
lean_dec(v_a_1229_);
v_a_1229_ = v___x_1236_;
v_b_1230_ = v_a_1234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1253_, lean_object* v_args_1254_, lean_object* v_origAllocId_1255_, lean_object* v_resetTokenId_1256_, lean_object* v_a_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1253_, v_args_1254_, v_origAllocId_1255_, v_resetTokenId_1256_, v_a_1257_, v_b_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec(v_origAllocId_1255_);
lean_dec_ref(v_args_1254_);
lean_dec(v_upperBound_1253_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(lean_object* v_resetTokenId_1262_, lean_object* v_info_1263_, uint8_t v_update_1264_, lean_object* v_args_1265_, lean_object* v_contJpId_1266_, lean_object* v_origAllocId_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_code_1279_; lean_object* v___x_1280_; 
lean_inc_n(v_resetTokenId_1262_, 2);
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_resetTokenId_1262_);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_array_get_size(v_args_1265_);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_mk_empty_array_with_capacity(v___x_1276_);
v___x_1278_ = lean_array_push(v___x_1277_, v___x_1273_);
v_code_1279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1279_, 0, v_contJpId_1266_);
lean_ctor_set(v_code_1279_, 1, v___x_1278_);
v___x_1280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v___x_1275_, v_args_1265_, v_origAllocId_1267_, v_resetTokenId_1262_, v___x_1274_, v_code_1279_, v_a_1269_);
if (lean_obj_tag(v___x_1280_) == 0)
{
if (v_update_1264_ == 0)
{
lean_dec(v_resetTokenId_1262_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1290_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_cidx_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v_cidx_1285_ = lean_ctor_get(v_info_1263_, 1);
lean_inc(v_cidx_1285_);
v___x_1286_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_1286_, 0, v_resetTokenId_1262_);
lean_ctor_set(v___x_1286_, 1, v_cidx_1285_);
lean_ctor_set(v___x_1286_, 2, v_a_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1286_);
v___x_1288_ = v___x_1283_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_dec(v_resetTokenId_1262_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath___boxed(lean_object* v_resetTokenId_1291_, lean_object* v_info_1292_, lean_object* v_update_1293_, lean_object* v_args_1294_, lean_object* v_contJpId_1295_, lean_object* v_origAllocId_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
uint8_t v_update_boxed_1302_; lean_object* v_res_1303_; 
v_update_boxed_1302_ = lean_unbox(v_update_1293_);
v_res_1303_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1291_, v_info_1292_, v_update_boxed_1302_, v_args_1294_, v_contJpId_1295_, v_origAllocId_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_origAllocId_1296_);
lean_dec_ref(v_args_1294_);
lean_dec_ref(v_info_1292_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(lean_object* v_upperBound_1304_, lean_object* v_args_1305_, lean_object* v_origAllocId_1306_, lean_object* v_resetTokenId_1307_, lean_object* v_inst_1308_, lean_object* v_R_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_, lean_object* v_c_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___redArg(v_upperBound_1304_, v_args_1305_, v_origAllocId_1306_, v_resetTokenId_1307_, v_a_1310_, v_b_1311_, v___y_1314_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1319_, lean_object* v_args_1320_, lean_object* v_origAllocId_1321_, lean_object* v_resetTokenId_1322_, lean_object* v_inst_1323_, lean_object* v_R_1324_, lean_object* v_a_1325_, lean_object* v_b_1326_, lean_object* v_c_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath_spec__0(v_upperBound_1319_, v_args_1320_, v_origAllocId_1321_, v_resetTokenId_1322_, v_inst_1323_, v_R_1324_, v_a_1325_, v_b_1326_, v_c_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v_origAllocId_1321_);
lean_dec_ref(v_args_1320_);
lean_dec(v_upperBound_1319_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(lean_object* v_decl_1337_, lean_object* v_info_1338_, lean_object* v_args_1339_, lean_object* v_contJpId_1340_, lean_object* v_selfSets_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___closed__1));
v___x_1348_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1347_, v_a_1343_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v_type_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v_type_1350_ = lean_ctor_get(v_decl_1337_, 2);
lean_inc_ref(v_type_1350_);
lean_dec_ref(v_decl_1337_);
v___x_1351_ = 1;
v___x_1352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_info_1338_);
lean_ctor_set(v___x_1352_, 1, v_args_1339_);
v___x_1353_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1351_, v_a_1349_, v_type_1350_, v___x_1352_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_fvarId_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1371_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v_fvarId_1355_ = lean_ctor_get(v_a_1354_, 0);
lean_inc_n(v_fvarId_1355_, 2);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_fvarId_1355_);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_mk_empty_array_with_capacity(v___x_1357_);
v___x_1359_ = lean_array_push(v___x_1358_, v___x_1356_);
v___x_1360_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_contJpId_1340_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1355_, v_selfSets_1341_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1371_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1366_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1362_, v___x_1360_);
lean_dec(v_a_1362_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_a_1354_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1367_);
v___x_1369_ = v___x_1364_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v_selfSets_1341_);
lean_dec(v_contJpId_1340_);
v_a_1372_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1353_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1353_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v_selfSets_1341_);
lean_dec(v_contJpId_1340_);
lean_dec_ref(v_args_1339_);
lean_dec_ref(v_info_1338_);
lean_dec_ref(v_decl_1337_);
v_a_1380_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1348_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1348_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath___boxed(lean_object* v_decl_1388_, lean_object* v_info_1389_, lean_object* v_args_1390_, lean_object* v_contJpId_1391_, lean_object* v_selfSets_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1388_, v_info_1389_, v_args_1390_, v_contJpId_1391_, v_selfSets_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(lean_object* v_alt_1399_, lean_object* v_f_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___y_1407_; 
switch(lean_obj_tag(v_alt_1399_))
{
case 0:
{
lean_object* v_code_1426_; 
v_code_1426_ = lean_ctor_get(v_alt_1399_, 2);
lean_inc_ref(v_code_1426_);
v___y_1407_ = v_code_1426_;
goto v___jp_1406_;
}
case 1:
{
lean_object* v_code_1427_; 
v_code_1427_ = lean_ctor_get(v_alt_1399_, 1);
lean_inc_ref(v_code_1427_);
v___y_1407_ = v_code_1427_;
goto v___jp_1406_;
}
default: 
{
lean_object* v_code_1428_; 
v_code_1428_ = lean_ctor_get(v_alt_1399_, 0);
lean_inc_ref(v_code_1428_);
v___y_1407_ = v_code_1428_;
goto v___jp_1406_;
}
}
v___jp_1406_:
{
lean_object* v___x_1408_; 
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
v___x_1408_ = lean_apply_6(v_f_1400_, v___y_1407_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, lean_box(0));
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1417_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1417_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1413_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1399_, v_a_1409_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1413_);
v___x_1415_ = v___x_1411_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_alt_1399_);
v_a_1418_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1408_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1408_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg___boxed(lean_object* v_alt_1429_, lean_object* v_f_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1429_, v_f_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(uint8_t v_pu_1437_, lean_object* v_alt_1438_, lean_object* v_f_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_alt_1438_, v_f_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___boxed(lean_object* v_pu_1446_, lean_object* v_alt_1447_, lean_object* v_f_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v_pu_boxed_1454_; lean_object* v_res_1455_; 
v_pu_boxed_1454_ = lean_unbox(v_pu_1446_);
v_res_1455_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0(v_pu_boxed_1454_, v_alt_1447_, v_f_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1455_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_toApplicative_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1498_; 
v___x_1463_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1464_ = l_StateRefT_x27_instMonad___redArg(v___x_1463_);
v_toApplicative_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v___x_1464_, 1);
lean_dec(v_unused_1499_);
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1498_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_toApplicative_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1498_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_toFunctor_1469_; lean_object* v_toSeq_1470_; lean_object* v_toSeqLeft_1471_; lean_object* v_toSeqRight_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1496_; 
v_toFunctor_1469_ = lean_ctor_get(v_toApplicative_1465_, 0);
v_toSeq_1470_ = lean_ctor_get(v_toApplicative_1465_, 2);
v_toSeqLeft_1471_ = lean_ctor_get(v_toApplicative_1465_, 3);
v_toSeqRight_1472_ = lean_ctor_get(v_toApplicative_1465_, 4);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_toApplicative_1465_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_toApplicative_1465_, 1);
lean_dec(v_unused_1497_);
v___x_1474_ = v_toApplicative_1465_;
v_isShared_1475_ = v_isSharedCheck_1496_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_toSeqRight_1472_);
lean_inc(v_toSeqLeft_1471_);
lean_inc(v_toSeq_1470_);
lean_inc(v_toFunctor_1469_);
lean_dec(v_toApplicative_1465_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1496_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___f_1476_; lean_object* v___f_1477_; lean_object* v___f_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; lean_object* v___f_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; lean_object* v___x_1485_; 
v___f_1476_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1477_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1469_);
v___f_1478_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1478_, 0, v_toFunctor_1469_);
v___f_1479_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1479_, 0, v_toFunctor_1469_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___f_1478_);
lean_ctor_set(v___x_1480_, 1, v___f_1479_);
v___f_1481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1481_, 0, v_toSeqRight_1472_);
v___f_1482_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1482_, 0, v_toSeqLeft_1471_);
v___f_1483_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1483_, 0, v_toSeq_1470_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v___f_1481_);
lean_ctor_set(v___x_1474_, 3, v___f_1482_);
lean_ctor_set(v___x_1474_, 2, v___f_1483_);
lean_ctor_set(v___x_1474_, 1, v___f_1476_);
lean_ctor_set(v___x_1474_, 0, v___x_1480_);
v___x_1485_ = v___x_1474_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___f_1476_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v___f_1483_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v___f_1482_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v___f_1481_);
v___x_1485_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___f_1477_);
lean_ctor_set(v___x_1467_, 0, v___x_1485_);
v___x_1487_ = v___x_1467_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___f_1477_);
v___x_1487_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_6838__overap_1492_; lean_object* v___x_1493_; 
v___x_1488_ = l_StateRefT_x27_instMonad___redArg(v___x_1487_);
v___x_1489_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1490_ = l_instInhabitedOfMonad___redArg(v___x_1488_, v___x_1489_);
v___f_1491_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1491_, 0, v___x_1490_);
v___x_6838__overap_1492_ = lean_panic_fn_borrowed(v___f_1491_, v_msg_1457_);
lean_dec_ref(v___f_1491_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
v___x_1493_ = lean_apply_5(v___x_6838__overap_1492_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, lean_box(0));
return v___x_1493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1506_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1515_ = l_Lean_Expr_const___override(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1516_, lean_object* v_origAllocId_1517_, lean_object* v_isSharedId_1518_, lean_object* v_resultType_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1516_, v_origAllocId_1517_, v_isSharedId_1518_, v_resultType_1519_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1527_, lean_object* v_origAllocId_1528_, lean_object* v_isSharedId_1529_, lean_object* v_resultType_1530_, lean_object* v_i_1531_, lean_object* v_as_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = lean_array_get_size(v_as_1532_);
v___x_1539_ = lean_nat_dec_lt(v_i_1531_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_dec(v_i_1531_);
lean_dec_ref(v_resultType_1530_);
lean_dec(v_isSharedId_1529_);
lean_dec(v_origAllocId_1528_);
lean_dec(v_resetTokenId_1527_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_as_1532_);
return v___x_1540_;
}
else
{
lean_object* v___f_1541_; lean_object* v_a_1542_; lean_object* v___x_1543_; 
lean_inc_ref(v_resultType_1530_);
lean_inc(v_isSharedId_1529_);
lean_inc(v_origAllocId_1528_);
lean_inc(v_resetTokenId_1527_);
v___f_1541_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1541_, 0, v_resetTokenId_1527_);
lean_closure_set(v___f_1541_, 1, v_origAllocId_1528_);
lean_closure_set(v___f_1541_, 2, v_isSharedId_1529_);
lean_closure_set(v___f_1541_, 3, v_resultType_1530_);
v_a_1542_ = lean_array_fget_borrowed(v_as_1532_, v_i_1531_);
lean_inc(v_a_1542_);
v___x_1543_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1542_, v___f_1541_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; size_t v___x_1545_; size_t v___x_1546_; uint8_t v___x_1547_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = lean_ptr_addr(v_a_1542_);
v___x_1546_ = lean_ptr_addr(v_a_1544_);
v___x_1547_ = lean_usize_dec_eq(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_nat_add(v_i_1531_, v___x_1548_);
v___x_1550_ = lean_array_fset(v_as_1532_, v_i_1531_, v_a_1544_);
lean_dec(v_i_1531_);
v_i_1531_ = v___x_1549_;
v_as_1532_ = v___x_1550_;
goto _start;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_a_1544_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_add(v_i_1531_, v___x_1552_);
lean_dec(v_i_1531_);
v_i_1531_ = v___x_1553_;
goto _start;
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_as_1532_);
lean_dec(v_i_1531_);
lean_dec_ref(v_resultType_1530_);
lean_dec(v_isSharedId_1529_);
lean_dec(v_origAllocId_1528_);
lean_dec(v_resetTokenId_1527_);
v_a_1555_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1543_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1543_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1566_ = lean_unsigned_to_nat(6u);
v___x_1567_ = lean_unsigned_to_nat(208u);
v___x_1568_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1569_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_1570_ = l_mkPanicMessageWithDecl(v___x_1569_, v___x_1568_, v___x_1567_, v___x_1566_, v___x_1565_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1571_, lean_object* v_code_1572_, lean_object* v_origAllocId_1573_, lean_object* v_isSharedId_1574_, lean_object* v_currentRetType_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
switch(lean_obj_tag(v_code_1572_))
{
case 0:
{
lean_object* v_decl_1581_; lean_object* v_value_1582_; 
v_decl_1581_ = lean_ctor_get(v_code_1572_, 0);
v_value_1582_ = lean_ctor_get(v_decl_1581_, 3);
lean_inc(v_value_1582_);
if (lean_obj_tag(v_value_1582_) == 12)
{
lean_object* v_k_1583_; lean_object* v_fvarId_1584_; lean_object* v_binderName_1585_; lean_object* v_type_1586_; lean_object* v_var_1587_; lean_object* v_i_1588_; uint8_t v_updateHeader_1589_; lean_object* v_args_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1706_; 
v_k_1583_ = lean_ctor_get(v_code_1572_, 1);
v_fvarId_1584_ = lean_ctor_get(v_decl_1581_, 0);
v_binderName_1585_ = lean_ctor_get(v_decl_1581_, 1);
v_type_1586_ = lean_ctor_get(v_decl_1581_, 2);
v_var_1587_ = lean_ctor_get(v_value_1582_, 0);
v_i_1588_ = lean_ctor_get(v_value_1582_, 1);
v_updateHeader_1589_ = lean_ctor_get_uint8(v_value_1582_, sizeof(void*)*3);
v_args_1590_ = lean_ctor_get(v_value_1582_, 2);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_value_1582_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1592_ = v_value_1582_;
v_isShared_1593_ = v_isSharedCheck_1706_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_args_1590_);
lean_inc(v_i_1588_);
lean_inc(v_var_1587_);
lean_dec(v_value_1582_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1706_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1571_, v_var_1587_);
lean_dec(v_var_1587_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
lean_del_object(v___x_1592_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
lean_inc_ref(v_k_1583_);
v___x_1595_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1583_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1618_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1618_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1618_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
size_t v___x_1600_; size_t v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = lean_ptr_addr(v_k_1583_);
v___x_1601_ = lean_ptr_addr(v_a_1596_);
v___x_1602_ = lean_usize_dec_eq(v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1612_; 
lean_inc_ref(v_decl_1581_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1613_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1614_);
v___x_1604_ = v_code_1572_;
v_isShared_1605_ = v_isSharedCheck_1612_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v_code_1572_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1612_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v_a_1596_);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_decl_1581_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1596_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1607_);
v___x_1609_ = v___x_1598_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v___x_1616_; 
lean_dec(v_a_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v_code_1572_);
v___x_1616_ = v___x_1598_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_code_1572_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 2);
return v___x_1595_;
}
}
else
{
lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1703_; 
lean_inc_ref(v_k_1583_);
lean_inc_ref(v_decl_1581_);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; 
v_unused_1704_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1705_);
v___x_1620_ = v_code_1572_;
v_isShared_1621_ = v_isSharedCheck_1703_;
goto v_resetjp_1619_;
}
else
{
lean_dec(v_code_1572_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1703_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
uint8_t v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = 0;
v___x_1623_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1584_, v_k_1583_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
lean_inc(v_fst_1625_);
v_snd_1626_ = lean_ctor_get(v_a_1624_, 1);
lean_inc(v_snd_1626_);
lean_dec(v_a_1624_);
v___x_1627_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1573_, v_fst_1625_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_fst_1625_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v_fst_1629_; lean_object* v_snd_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v_fst_1629_ = lean_ctor_get(v_a_1628_, 0);
lean_inc(v_fst_1629_);
v_snd_1630_ = lean_ctor_get(v_a_1628_, 1);
lean_inc(v_snd_1630_);
lean_dec(v_a_1628_);
v___x_1631_ = 1;
v___x_1632_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_snd_1630_, v_snd_1626_);
lean_dec(v_snd_1630_);
lean_inc_ref(v_type_1586_);
lean_inc(v_binderName_1585_);
lean_inc(v_fvarId_1584_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 0);
lean_ctor_set(v___x_1592_, 2, v_type_1586_);
lean_ctor_set(v___x_1592_, 1, v_binderName_1585_);
lean_ctor_set(v___x_1592_, 0, v_fvarId_1584_);
v___x_1634_ = v___x_1592_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_fvarId_1584_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_binderName_1585_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_type_1586_);
v___x_1634_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3, v___x_1622_);
v___x_1635_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1636_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1635_, v_a_1577_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_mk_empty_array_with_capacity(v___x_1638_);
v___x_1640_ = lean_array_push(v___x_1639_, v___x_1634_);
lean_inc_ref(v_currentRetType_1575_);
v___x_1641_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1631_, v_a_1637_, v_currentRetType_1575_, v___x_1640_, v___x_1632_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_fvarId_1643_; lean_object* v___x_1644_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_fvarId_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_fvarId_1643_);
lean_inc_ref(v_args_1590_);
lean_inc_ref(v_i_1588_);
lean_inc_ref(v_decl_1581_);
v___x_1644_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1581_, v_i_1588_, v_args_1590_, v_fvarId_1643_, v_fst_1629_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
lean_inc(v_fvarId_1643_);
v___x_1646_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1571_, v_i_1588_, v_updateHeader_1589_, v_args_1590_, v_fvarId_1643_, v_origAllocId_1573_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_origAllocId_1573_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1648_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1631_, v_decl_1581_, v_a_1577_);
lean_dec_ref(v_decl_1581_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref_known(v___x_1648_, 1);
v___x_1649_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1650_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1574_, v___x_1649_, v_currentRetType_1575_, v_a_1645_, v_a_1647_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1661_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1661_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1661_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 2);
lean_ctor_set(v___x_1620_, 1, v_a_1651_);
lean_ctor_set(v___x_1620_, 0, v_a_1642_);
v___x_1656_ = v___x_1620_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1642_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
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
lean_dec(v_a_1642_);
lean_del_object(v___x_1620_);
return v___x_1650_;
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_a_1647_);
lean_dec(v_a_1645_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1620_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
v_a_1662_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1648_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1648_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_dec(v_a_1645_);
lean_dec(v_a_1642_);
lean_del_object(v___x_1620_);
lean_dec_ref(v_decl_1581_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
return v___x_1646_;
}
}
else
{
lean_dec(v_a_1642_);
lean_del_object(v___x_1620_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
lean_dec_ref(v_decl_1581_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
return v___x_1644_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_fst_1629_);
lean_del_object(v___x_1620_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
lean_dec_ref(v_decl_1581_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
v_a_1670_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1641_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1641_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1632_);
lean_dec(v_fst_1629_);
lean_del_object(v___x_1620_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
lean_dec_ref(v_decl_1581_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
v_a_1678_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1636_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1636_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_snd_1626_);
lean_del_object(v___x_1620_);
lean_del_object(v___x_1592_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
lean_dec_ref(v_decl_1581_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
v_a_1687_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1627_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1627_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_del_object(v___x_1620_);
lean_del_object(v___x_1592_);
lean_dec_ref(v_args_1590_);
lean_dec_ref(v_i_1588_);
lean_dec_ref(v_decl_1581_);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
v_a_1695_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1623_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1623_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
}
else
{
lean_object* v_k_1707_; lean_object* v___x_1708_; 
lean_dec(v_value_1582_);
v_k_1707_ = lean_ctor_get(v_code_1572_, 1);
lean_inc_ref(v_k_1707_);
v___x_1708_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1707_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1731_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1731_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1731_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
size_t v___x_1713_; size_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1713_ = lean_ptr_addr(v_k_1707_);
v___x_1714_ = lean_ptr_addr(v_a_1709_);
v___x_1715_ = lean_usize_dec_eq(v___x_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
lean_inc_ref(v_decl_1581_);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; lean_object* v_unused_1727_; 
v_unused_1726_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1726_);
v_unused_1727_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1727_);
v___x_1717_ = v_code_1572_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_dec(v_code_1572_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v_a_1709_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_decl_1581_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_a_1709_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1720_);
v___x_1722_ = v___x_1711_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_object* v___x_1729_; 
lean_dec(v_a_1709_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v_code_1572_);
v___x_1729_ = v___x_1711_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_code_1572_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 2);
return v___x_1708_;
}
}
}
case 2:
{
lean_object* v_decl_1732_; lean_object* v_k_1733_; lean_object* v_params_1734_; lean_object* v_type_1735_; lean_object* v_value_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v_decl_1732_ = lean_ctor_get(v_code_1572_, 0);
v_k_1733_ = lean_ctor_get(v_code_1572_, 1);
v_params_1734_ = lean_ctor_get(v_decl_1732_, 2);
v_type_1735_ = lean_ctor_get(v_decl_1732_, 3);
v_value_1736_ = lean_ctor_get(v_decl_1732_, 4);
v___x_1737_ = 1;
lean_inc_ref(v_type_1735_);
lean_inc(v_isSharedId_1574_);
lean_inc(v_origAllocId_1573_);
lean_inc_ref(v_value_1736_);
lean_inc(v_resetTokenId_1571_);
v___x_1738_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_value_1736_, v_origAllocId_1573_, v_isSharedId_1574_, v_type_1735_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
lean_inc_ref(v_params_1734_);
lean_inc_ref(v_type_1735_);
lean_inc_ref(v_decl_1732_);
v___x_1740_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1737_, v_decl_1732_, v_type_1735_, v_params_1734_, v_a_1739_, v_a_1577_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
lean_inc_ref(v_k_1733_);
v___x_1742_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1733_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1780_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1780_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1780_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
size_t v___x_1747_; size_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = lean_ptr_addr(v_k_1733_);
v___x_1748_ = lean_ptr_addr(v_a_1743_);
v___x_1749_ = lean_usize_dec_eq(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1759_; 
v_isSharedCheck_1759_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; 
v_unused_1760_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1761_);
v___x_1751_ = v_code_1572_;
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
else
{
lean_dec(v_code_1572_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v_a_1743_);
lean_ctor_set(v___x_1751_, 0, v_a_1741_);
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1741_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_a_1743_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1754_);
v___x_1756_ = v___x_1745_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
size_t v___x_1762_; size_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = lean_ptr_addr(v_decl_1732_);
v___x_1763_ = lean_ptr_addr(v_a_1741_);
v___x_1764_ = lean_usize_dec_eq(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1774_; 
v_isSharedCheck_1774_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1775_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1776_);
v___x_1766_ = v_code_1572_;
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v_code_1572_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v_a_1743_);
lean_ctor_set(v___x_1766_, 0, v_a_1741_);
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1741_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_a_1743_);
v___x_1769_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1769_);
v___x_1771_ = v___x_1745_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v_a_1743_);
lean_dec(v_a_1741_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v_code_1572_);
v___x_1778_ = v___x_1745_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_code_1572_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
else
{
lean_dec(v_a_1741_);
lean_dec_ref_known(v_code_1572_, 2);
return v___x_1742_;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref_known(v_code_1572_, 2);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
v_a_1781_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1740_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1740_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 2);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
return v___x_1738_;
}
}
case 4:
{
lean_object* v_cases_1789_; lean_object* v_typeName_1790_; lean_object* v_resultType_1791_; lean_object* v_discr_1792_; lean_object* v_alts_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1832_; 
lean_dec_ref(v_currentRetType_1575_);
v_cases_1789_ = lean_ctor_get(v_code_1572_, 0);
lean_inc_ref(v_cases_1789_);
v_typeName_1790_ = lean_ctor_get(v_cases_1789_, 0);
v_resultType_1791_ = lean_ctor_get(v_cases_1789_, 1);
v_discr_1792_ = lean_ctor_get(v_cases_1789_, 2);
v_alts_1793_ = lean_ctor_get(v_cases_1789_, 3);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_cases_1789_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1795_ = v_cases_1789_;
v_isShared_1796_ = v_isSharedCheck_1832_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_alts_1793_);
lean_inc(v_discr_1792_);
lean_inc(v_resultType_1791_);
lean_inc(v_typeName_1790_);
lean_dec(v_cases_1789_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1832_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1793_);
lean_inc_ref(v_resultType_1791_);
v___x_1798_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1571_, v_origAllocId_1573_, v_isSharedId_1574_, v_resultType_1791_, v___x_1797_, v_alts_1793_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1823_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1823_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1823_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
size_t v___x_1803_; size_t v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = lean_ptr_addr(v_alts_1793_);
lean_dec_ref(v_alts_1793_);
v___x_1804_ = lean_ptr_addr(v_a_1799_);
v___x_1805_ = lean_usize_dec_eq(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1818_; 
v_isSharedCheck_1818_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1819_);
v___x_1807_ = v_code_1572_;
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v_code_1572_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 3, v_a_1799_);
v___x_1810_ = v___x_1795_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_typeName_1790_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_resultType_1791_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_discr_1792_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_a_1799_);
v___x_1810_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1812_);
v___x_1814_ = v___x_1801_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec(v_a_1799_);
lean_del_object(v___x_1795_);
lean_dec(v_discr_1792_);
lean_dec_ref(v_resultType_1791_);
lean_dec(v_typeName_1790_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v_code_1572_);
v___x_1821_ = v___x_1801_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_code_1572_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_del_object(v___x_1795_);
lean_dec_ref(v_alts_1793_);
lean_dec(v_discr_1792_);
lean_dec_ref(v_resultType_1791_);
lean_dec(v_typeName_1790_);
lean_dec_ref_known(v_code_1572_, 1);
v_a_1824_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1798_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1798_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1833_; lean_object* v_i_1834_; lean_object* v_y_1835_; lean_object* v_k_1836_; lean_object* v___x_1837_; 
v_fvarId_1833_ = lean_ctor_get(v_code_1572_, 0);
v_i_1834_ = lean_ctor_get(v_code_1572_, 1);
v_y_1835_ = lean_ctor_get(v_code_1572_, 2);
v_k_1836_ = lean_ctor_get(v_code_1572_, 3);
lean_inc_ref(v_k_1836_);
v___x_1837_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1836_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1862_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1862_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
size_t v___x_1842_; size_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = lean_ptr_addr(v_k_1836_);
v___x_1843_ = lean_ptr_addr(v_a_1838_);
v___x_1844_ = lean_usize_dec_eq(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1854_; 
lean_inc(v_y_1835_);
lean_inc(v_i_1834_);
lean_inc(v_fvarId_1833_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1855_ = lean_ctor_get(v_code_1572_, 3);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_code_1572_, 2);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1858_);
v___x_1846_ = v_code_1572_;
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
else
{
lean_dec(v_code_1572_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 3, v_a_1838_);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_fvarId_1833_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_i_1834_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_y_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_a_1838_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1849_);
v___x_1851_ = v___x_1840_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v___x_1860_; 
lean_dec(v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_code_1572_);
v___x_1860_ = v___x_1840_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_code_1572_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 4);
return v___x_1837_;
}
}
case 8:
{
lean_object* v_fvarId_1863_; lean_object* v_i_1864_; lean_object* v_y_1865_; lean_object* v_k_1866_; lean_object* v___x_1867_; 
v_fvarId_1863_ = lean_ctor_get(v_code_1572_, 0);
v_i_1864_ = lean_ctor_get(v_code_1572_, 1);
v_y_1865_ = lean_ctor_get(v_code_1572_, 2);
v_k_1866_ = lean_ctor_get(v_code_1572_, 3);
lean_inc_ref(v_k_1866_);
v___x_1867_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1866_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1892_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1892_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1892_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
size_t v___x_1872_; size_t v___x_1873_; uint8_t v___x_1874_; 
v___x_1872_ = lean_ptr_addr(v_k_1866_);
v___x_1873_ = lean_ptr_addr(v_a_1868_);
v___x_1874_ = lean_usize_dec_eq(v___x_1872_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1884_; 
lean_inc(v_y_1865_);
lean_inc(v_i_1864_);
lean_inc(v_fvarId_1863_);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; lean_object* v_unused_1886_; lean_object* v_unused_1887_; lean_object* v_unused_1888_; 
v_unused_1885_ = lean_ctor_get(v_code_1572_, 3);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_code_1572_, 2);
lean_dec(v_unused_1886_);
v_unused_1887_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1887_);
v_unused_1888_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1888_);
v___x_1876_ = v_code_1572_;
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v_code_1572_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 3, v_a_1868_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_fvarId_1863_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_i_1864_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_y_1865_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_a_1868_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1879_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v___x_1890_; 
lean_dec(v_a_1868_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_code_1572_);
v___x_1890_ = v___x_1870_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_code_1572_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 4);
return v___x_1867_;
}
}
case 9:
{
lean_object* v_fvarId_1893_; lean_object* v_i_1894_; lean_object* v_offset_1895_; lean_object* v_y_1896_; lean_object* v_ty_1897_; lean_object* v_k_1898_; lean_object* v___x_1899_; 
v_fvarId_1893_ = lean_ctor_get(v_code_1572_, 0);
v_i_1894_ = lean_ctor_get(v_code_1572_, 1);
v_offset_1895_ = lean_ctor_get(v_code_1572_, 2);
v_y_1896_ = lean_ctor_get(v_code_1572_, 3);
v_ty_1897_ = lean_ctor_get(v_code_1572_, 4);
v_k_1898_ = lean_ctor_get(v_code_1572_, 5);
lean_inc_ref(v_k_1898_);
v___x_1899_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1898_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1926_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1926_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1926_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
size_t v___x_1904_; size_t v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = lean_ptr_addr(v_k_1898_);
v___x_1905_ = lean_ptr_addr(v_a_1900_);
v___x_1906_ = lean_usize_dec_eq(v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1916_; 
lean_inc_ref(v_ty_1897_);
lean_inc(v_y_1896_);
lean_inc(v_offset_1895_);
lean_inc(v_i_1894_);
lean_inc(v_fvarId_1893_);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; lean_object* v_unused_1921_; lean_object* v_unused_1922_; 
v_unused_1917_ = lean_ctor_get(v_code_1572_, 5);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_code_1572_, 4);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_code_1572_, 3);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_code_1572_, 2);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1922_);
v___x_1908_ = v_code_1572_;
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
else
{
lean_dec(v_code_1572_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 5, v_a_1900_);
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_fvarId_1893_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_i_1894_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_offset_1895_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_y_1896_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_ty_1897_);
lean_ctor_set(v_reuseFailAlloc_1915_, 5, v_a_1900_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1911_);
v___x_1913_ = v___x_1902_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v___x_1924_; 
lean_dec(v_a_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_code_1572_);
v___x_1924_ = v___x_1902_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_code_1572_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 6);
return v___x_1899_;
}
}
case 10:
{
lean_object* v_fvarId_1927_; lean_object* v_cidx_1928_; lean_object* v_k_1929_; lean_object* v___x_1930_; 
v_fvarId_1927_ = lean_ctor_get(v_code_1572_, 0);
v_cidx_1928_ = lean_ctor_get(v_code_1572_, 1);
v_k_1929_ = lean_ctor_get(v_code_1572_, 2);
lean_inc_ref(v_k_1929_);
v___x_1930_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1929_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1954_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1954_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1954_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
size_t v___x_1935_; size_t v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_ptr_addr(v_k_1929_);
v___x_1936_ = lean_ptr_addr(v_a_1931_);
v___x_1937_ = lean_usize_dec_eq(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1947_; 
lean_inc(v_cidx_1928_);
lean_inc(v_fvarId_1927_);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; lean_object* v_unused_1949_; lean_object* v_unused_1950_; 
v_unused_1948_ = lean_ctor_get(v_code_1572_, 2);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1950_);
v___x_1939_ = v_code_1572_;
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v_code_1572_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 2, v_a_1931_);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_fvarId_1927_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_cidx_1928_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_a_1931_);
v___x_1942_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1942_);
v___x_1944_ = v___x_1933_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v___x_1952_; 
lean_dec(v_a_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v_code_1572_);
v___x_1952_ = v___x_1933_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_code_1572_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 3);
return v___x_1930_;
}
}
case 11:
{
lean_object* v_fvarId_1955_; lean_object* v_n_1956_; uint8_t v_check_1957_; uint8_t v_persistent_1958_; lean_object* v_k_1959_; lean_object* v___x_1960_; 
v_fvarId_1955_ = lean_ctor_get(v_code_1572_, 0);
v_n_1956_ = lean_ctor_get(v_code_1572_, 1);
v_check_1957_ = lean_ctor_get_uint8(v_code_1572_, sizeof(void*)*3);
v_persistent_1958_ = lean_ctor_get_uint8(v_code_1572_, sizeof(void*)*3 + 1);
v_k_1959_ = lean_ctor_get(v_code_1572_, 2);
lean_inc_ref(v_k_1959_);
v___x_1960_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1959_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1984_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1984_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1984_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
size_t v___x_1965_; size_t v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = lean_ptr_addr(v_k_1959_);
v___x_1966_ = lean_ptr_addr(v_a_1961_);
v___x_1967_ = lean_usize_dec_eq(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1977_; 
lean_inc(v_n_1956_);
lean_inc(v_fvarId_1955_);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; lean_object* v_unused_1979_; lean_object* v_unused_1980_; 
v_unused_1978_ = lean_ctor_get(v_code_1572_, 2);
lean_dec(v_unused_1978_);
v_unused_1979_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_1980_);
v___x_1969_ = v_code_1572_;
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
else
{
lean_dec(v_code_1572_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 2, v_a_1961_);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_fvarId_1955_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_n_1956_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_a_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*3, v_check_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*3 + 1, v_persistent_1958_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1972_);
v___x_1974_ = v___x_1963_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_a_1961_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_code_1572_);
v___x_1982_ = v___x_1963_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_code_1572_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 3);
return v___x_1960_;
}
}
case 12:
{
lean_object* v_fvarId_1985_; lean_object* v_n_1986_; uint8_t v_check_1987_; uint8_t v_persistent_1988_; lean_object* v_objs_x3f_1989_; lean_object* v_k_1990_; uint8_t v___x_1991_; 
v_fvarId_1985_ = lean_ctor_get(v_code_1572_, 0);
v_n_1986_ = lean_ctor_get(v_code_1572_, 1);
v_check_1987_ = lean_ctor_get_uint8(v_code_1572_, sizeof(void*)*4);
v_persistent_1988_ = lean_ctor_get_uint8(v_code_1572_, sizeof(void*)*4 + 1);
v_objs_x3f_1989_ = lean_ctor_get(v_code_1572_, 2);
v_k_1990_ = lean_ctor_get(v_code_1572_, 3);
v___x_1991_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1571_, v_fvarId_1985_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_inc_ref(v_k_1990_);
v___x_1992_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_1990_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2017_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2017_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2017_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
size_t v___x_1997_; size_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = lean_ptr_addr(v_k_1990_);
v___x_1998_ = lean_ptr_addr(v_a_1993_);
v___x_1999_ = lean_usize_dec_eq(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
lean_inc(v_objs_x3f_1989_);
lean_inc(v_n_1986_);
lean_inc(v_fvarId_1985_);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; lean_object* v_unused_2011_; lean_object* v_unused_2012_; lean_object* v_unused_2013_; 
v_unused_2010_ = lean_ctor_get(v_code_1572_, 3);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_code_1572_, 2);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_2013_);
v___x_2001_ = v_code_1572_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v_code_1572_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 3, v_a_1993_);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_fvarId_1985_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_n_1986_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_objs_x3f_1989_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_a_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*4, v_check_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*4 + 1, v_persistent_1988_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2004_);
v___x_2006_ = v___x_1995_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v___x_2015_; 
lean_dec(v_a_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v_code_1572_);
v___x_2015_ = v___x_1995_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_code_1572_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 4);
return v___x_1992_;
}
}
else
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
lean_inc_ref(v_k_1990_);
lean_inc(v_n_1986_);
lean_dec_ref_known(v_code_1572_, 4);
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_dec_eq(v_n_1986_, v___x_2018_);
lean_dec(v_n_1986_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec_ref(v_k_1990_);
lean_dec(v_resetTokenId_1571_);
v___x_2020_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_2021_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_2020_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_resetTokenId_1571_);
lean_ctor_set(v___x_2022_, 1, v_k_1990_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
case 13:
{
lean_object* v_fvarId_2024_; lean_object* v_k_2025_; lean_object* v___x_2026_; 
v_fvarId_2024_ = lean_ctor_get(v_code_1572_, 0);
v_k_2025_ = lean_ctor_get(v_code_1572_, 1);
lean_inc_ref(v_k_2025_);
v___x_2026_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1571_, v_k_2025_, v_origAllocId_1573_, v_isSharedId_1574_, v_currentRetType_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2049_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2049_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2049_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
size_t v___x_2031_; size_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2031_ = lean_ptr_addr(v_k_2025_);
v___x_2032_ = lean_ptr_addr(v_a_2027_);
v___x_2033_ = lean_usize_dec_eq(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2043_; 
lean_inc(v_fvarId_2024_);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_code_1572_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; lean_object* v_unused_2045_; 
v_unused_2044_ = lean_ctor_get(v_code_1572_, 1);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_code_1572_, 0);
lean_dec(v_unused_2045_);
v___x_2035_ = v_code_1572_;
v_isShared_2036_ = v_isSharedCheck_2043_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v_code_1572_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2043_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_a_2027_);
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_fvarId_2024_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_a_2027_);
v___x_2038_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2038_);
v___x_2040_ = v___x_2029_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v___x_2047_; 
lean_dec(v_a_2027_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v_code_1572_);
v___x_2047_ = v___x_2029_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_code_1572_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1572_, 2);
return v___x_2026_;
}
}
default: 
{
lean_object* v___x_2050_; 
lean_dec_ref(v_currentRetType_1575_);
lean_dec(v_isSharedId_1574_);
lean_dec(v_origAllocId_1573_);
lean_dec(v_resetTokenId_1571_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_code_1572_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_2051_, lean_object* v_origAllocId_2052_, lean_object* v_isSharedId_2053_, lean_object* v_resultType_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2051_, v_x_2055_, v_origAllocId_2052_, v_isSharedId_2053_, v_resultType_2054_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_2062_, lean_object* v_origAllocId_2063_, lean_object* v_isSharedId_2064_, lean_object* v_resultType_2065_, lean_object* v_i_2066_, lean_object* v_as_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_2062_, v_origAllocId_2063_, v_isSharedId_2064_, v_resultType_2065_, v_i_2066_, v_as_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_2074_, lean_object* v_code_2075_, lean_object* v_origAllocId_2076_, lean_object* v_isSharedId_2077_, lean_object* v_currentRetType_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2074_, v_code_2075_, v_origAllocId_2076_, v_isSharedId_2077_, v_currentRetType_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2094_, lean_object* v_ds_2095_, lean_object* v_decl_2096_, lean_object* v_nFields_2097_, lean_object* v_origAllocId_2098_, lean_object* v_k_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2097_, v_origAllocId_2098_, v_ds_2095_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v_fst_2107_; lean_object* v_snd_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2229_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v_fst_2107_ = lean_ctor_get(v_a_2106_, 0);
v_snd_2108_ = lean_ctor_get(v_a_2106_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_a_2106_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2110_ = v_a_2106_;
v_isShared_2111_ = v_isSharedCheck_2229_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_snd_2108_);
lean_inc(v_fst_2107_);
lean_dec(v_a_2106_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2229_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2113_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2112_, v_a_2101_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = 1;
v___x_2116_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2117_ = 0;
v___x_2118_ = l_Lean_Compiler_LCNF_mkParam(v___x_2115_, v_a_2114_, v___x_2116_, v___x_2117_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_fvarId_2120_; lean_object* v_binderName_2121_; lean_object* v_fvarId_2122_; lean_object* v___x_2123_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v_fvarId_2120_ = lean_ctor_get(v_decl_2096_, 0);
v_binderName_2121_ = lean_ctor_get(v_decl_2096_, 1);
v_fvarId_2122_ = lean_ctor_get(v_a_2119_, 0);
lean_inc_ref(v_currentRetType_2094_);
lean_inc(v_fvarId_2122_);
lean_inc(v_origAllocId_2098_);
lean_inc(v_fvarId_2120_);
v___x_2123_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2120_, v_k_2099_, v_origAllocId_2098_, v_fvarId_2122_, v_currentRetType_2094_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2094_);
v___x_2126_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2124_, v___x_2125_, v_currentRetType_2094_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2212_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2212_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2212_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2131_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2121_);
lean_inc(v_fvarId_2120_);
v___x_2132_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2132_, 0, v_fvarId_2120_);
lean_ctor_set(v___x_2132_, 1, v_binderName_2121_);
lean_ctor_set(v___x_2132_, 2, v___x_2131_);
lean_ctor_set_uint8(v___x_2132_, sizeof(void*)*3, v___x_2117_);
v___x_2133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2134_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2133_, v_a_2101_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = lean_unsigned_to_nat(2u);
v___x_2137_ = lean_mk_empty_array_with_capacity(v___x_2136_);
v___x_2138_ = lean_array_push(v___x_2137_, v___x_2132_);
v___x_2139_ = lean_array_push(v___x_2138_, v_a_2119_);
lean_inc_ref(v_currentRetType_2094_);
v___x_2140_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2115_, v_a_2135_, v_currentRetType_2094_, v___x_2139_, v_a_2127_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2143_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2142_, v_a_2101_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
lean_inc(v_origAllocId_2098_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set_tag(v___x_2129_, 15);
lean_ctor_set(v___x_2129_, 0, v_origAllocId_2098_);
v___x_2146_ = v___x_2129_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_origAllocId_2098_);
v___x_2146_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2115_, v_a_2144_, v___x_2116_, v___x_2146_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v_fvarId_2149_; lean_object* v_fvarId_2150_; lean_object* v___x_2151_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v_fvarId_2149_ = lean_ctor_get(v_a_2141_, 0);
v_fvarId_2150_ = lean_ctor_get(v_a_2148_, 0);
lean_inc(v_fvarId_2150_);
lean_inc(v_fvarId_2149_);
lean_inc(v_origAllocId_2098_);
v___x_2151_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2098_, v_snd_2108_, v_fvarId_2149_, v_fvarId_2150_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
lean_inc(v_fvarId_2150_);
lean_inc(v_fvarId_2149_);
v___x_2153_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2098_, v_snd_2108_, v_fvarId_2149_, v_fvarId_2150_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_snd_2108_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
lean_inc(v_fvarId_2150_);
v___x_2155_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2150_, v___x_2116_, v_currentRetType_2094_, v_a_2152_, v_a_2154_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v_a_2156_);
lean_ctor_set(v___x_2110_, 0, v_a_2148_);
v___x_2158_ = v___x_2110_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2148_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2156_);
v___x_2158_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2115_, v_decl_2096_, v_a_2101_);
lean_dec_ref(v_decl_2096_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2168_; 
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2169_);
v___x_2161_ = v___x_2159_;
v_isShared_2162_ = v_isSharedCheck_2168_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v___x_2159_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2168_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2141_);
lean_ctor_set(v___x_2163_, 1, v___x_2158_);
v___x_2164_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_2107_, v___x_2163_);
lean_dec(v_fst_2107_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2164_);
v___x_2166_ = v___x_2161_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v___x_2158_);
lean_dec(v_a_2141_);
lean_dec(v_fst_2107_);
v_a_2170_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2159_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2159_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
else
{
lean_dec(v_a_2148_);
lean_dec(v_a_2141_);
lean_del_object(v___x_2110_);
lean_dec(v_fst_2107_);
lean_dec_ref(v_decl_2096_);
return v___x_2155_;
}
}
else
{
lean_dec(v_a_2152_);
lean_dec(v_a_2148_);
lean_dec(v_a_2141_);
lean_del_object(v___x_2110_);
lean_dec(v_fst_2107_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
return v___x_2153_;
}
}
else
{
lean_dec(v_a_2148_);
lean_dec(v_a_2141_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
return v___x_2151_;
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2141_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2179_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2147_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2147_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2141_);
lean_del_object(v___x_2129_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2188_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2143_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2143_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_del_object(v___x_2129_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2196_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2140_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2140_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref_known(v___x_2132_, 3);
lean_del_object(v___x_2129_);
lean_dec(v_a_2127_);
lean_dec(v_a_2119_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2204_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2134_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2134_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
else
{
lean_dec(v_a_2119_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
return v___x_2126_;
}
}
else
{
lean_dec(v_a_2119_);
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
return v___x_2123_;
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec_ref(v_k_2099_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2213_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2118_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2118_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_del_object(v___x_2110_);
lean_dec(v_snd_2108_);
lean_dec(v_fst_2107_);
lean_dec_ref(v_k_2099_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2221_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2113_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2113_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_k_2099_);
lean_dec(v_origAllocId_2098_);
lean_dec_ref(v_decl_2096_);
lean_dec_ref(v_currentRetType_2094_);
v_a_2230_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2105_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2105_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2238_, v_x_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2246_, lean_object* v_i_2247_, lean_object* v_as_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = lean_array_get_size(v_as_2248_);
v___x_2255_ = lean_nat_dec_lt(v_i_2247_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
lean_dec(v_i_2247_);
lean_dec_ref(v_resultType_2246_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_as_2248_);
return v___x_2256_;
}
else
{
lean_object* v___f_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; 
lean_inc_ref(v_resultType_2246_);
v___f_2257_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2257_, 0, v_resultType_2246_);
v_a_2258_ = lean_array_fget_borrowed(v_as_2248_, v_i_2247_);
lean_inc(v_a_2258_);
v___x_2259_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2258_, v___f_2257_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; size_t v___x_2261_; size_t v___x_2262_; uint8_t v___x_2263_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = lean_ptr_addr(v_a_2258_);
v___x_2262_ = lean_ptr_addr(v_a_2260_);
v___x_2263_ = lean_usize_dec_eq(v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_add(v_i_2247_, v___x_2264_);
v___x_2266_ = lean_array_fset(v_as_2248_, v_i_2247_, v_a_2260_);
lean_dec(v_i_2247_);
v_i_2247_ = v___x_2265_;
v_as_2248_ = v___x_2266_;
goto _start;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec(v_a_2260_);
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_nat_add(v_i_2247_, v___x_2268_);
lean_dec(v_i_2247_);
v_i_2247_ = v___x_2269_;
goto _start;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v_as_2248_);
lean_dec(v_i_2247_);
lean_dec_ref(v_resultType_2246_);
v_a_2271_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2259_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2259_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2279_, lean_object* v_ds_2280_, lean_object* v_currentRetType_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_code_2288_; lean_object* v_ds_2289_; lean_object* v_k_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; 
switch(lean_obj_tag(v_code_2279_))
{
case 0:
{
lean_object* v_decl_2299_; lean_object* v_value_2300_; 
v_decl_2299_ = lean_ctor_get(v_code_2279_, 0);
v_value_2300_ = lean_ctor_get(v_decl_2299_, 3);
if (lean_obj_tag(v_value_2300_) == 11)
{
lean_object* v_k_2301_; lean_object* v_n_2302_; lean_object* v_var_2303_; lean_object* v___x_2304_; 
lean_inc_ref(v_decl_2299_);
v_k_2301_ = lean_ctor_get(v_code_2279_, 1);
lean_inc_ref(v_k_2301_);
lean_dec_ref_known(v_code_2279_, 2);
v_n_2302_ = lean_ctor_get(v_value_2300_, 0);
lean_inc(v_n_2302_);
v_var_2303_ = lean_ctor_get(v_value_2300_, 1);
lean_inc(v_var_2303_);
v___x_2304_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2281_, v_ds_2280_, v_decl_2299_, v_n_2302_, v_var_2303_, v_k_2301_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
return v___x_2304_;
}
else
{
lean_object* v_k_2305_; 
v_k_2305_ = lean_ctor_get(v_code_2279_, 1);
lean_inc_ref(v_k_2305_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2305_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
}
case 2:
{
lean_object* v_decl_2306_; lean_object* v_k_2307_; lean_object* v_params_2308_; lean_object* v_type_2309_; lean_object* v_value_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_decl_2306_ = lean_ctor_get(v_code_2279_, 0);
lean_inc_ref(v_decl_2306_);
v_k_2307_ = lean_ctor_get(v_code_2279_, 1);
lean_inc_ref(v_k_2307_);
lean_dec_ref_known(v_code_2279_, 2);
v_params_2308_ = lean_ctor_get(v_decl_2306_, 2);
lean_inc_ref(v_params_2308_);
v_type_2309_ = lean_ctor_get(v_decl_2306_, 3);
lean_inc_ref_n(v_type_2309_, 2);
v_value_2310_ = lean_ctor_get(v_decl_2306_, 4);
v___x_2311_ = 1;
v___x_2312_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2310_);
v___x_2313_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2310_, v___x_2312_, v_type_2309_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2333_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2333_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2333_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2311_, v_decl_2306_, v_type_2309_, v_params_2308_, v_a_2314_, v_a_2283_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
if (v_isShared_2317_ == 0)
{
lean_ctor_set_tag(v___x_2316_, 2);
lean_ctor_set(v___x_2316_, 0, v_a_2319_);
v___x_2321_ = v___x_2316_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2319_);
v___x_2321_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_array_push(v_ds_2280_, v___x_2321_);
v_code_2279_ = v_k_2307_;
v_ds_2280_ = v___x_2322_;
goto _start;
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_del_object(v___x_2316_);
lean_dec_ref(v_k_2307_);
lean_dec_ref(v_currentRetType_2281_);
lean_dec_ref(v_ds_2280_);
v_a_2325_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2318_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2318_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2309_);
lean_dec_ref(v_params_2308_);
lean_dec_ref(v_k_2307_);
lean_dec_ref(v_decl_2306_);
lean_dec_ref(v_currentRetType_2281_);
lean_dec_ref(v_ds_2280_);
return v___x_2313_;
}
}
case 4:
{
lean_object* v_cases_2334_; lean_object* v_typeName_2335_; lean_object* v_resultType_2336_; lean_object* v_discr_2337_; lean_object* v_alts_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_currentRetType_2281_);
v_cases_2334_ = lean_ctor_get(v_code_2279_, 0);
lean_inc_ref(v_cases_2334_);
v_typeName_2335_ = lean_ctor_get(v_cases_2334_, 0);
v_resultType_2336_ = lean_ctor_get(v_cases_2334_, 1);
v_discr_2337_ = lean_ctor_get(v_cases_2334_, 2);
v_alts_2338_ = lean_ctor_get(v_cases_2334_, 3);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_cases_2334_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2340_ = v_cases_2334_;
v_isShared_2341_ = v_isSharedCheck_2377_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_alts_2338_);
lean_inc(v_discr_2337_);
lean_inc(v_resultType_2336_);
lean_inc(v_typeName_2335_);
lean_dec(v_cases_2334_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2377_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2338_);
lean_inc_ref(v_resultType_2336_);
v___x_2343_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2336_, v___x_2342_, v_alts_2338_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2368_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2368_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2368_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___y_2349_; size_t v___x_2354_; size_t v___x_2355_; uint8_t v___x_2356_; 
v___x_2354_ = lean_ptr_addr(v_alts_2338_);
lean_dec_ref(v_alts_2338_);
v___x_2355_ = lean_ptr_addr(v_a_2344_);
v___x_2356_ = lean_usize_dec_eq(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2366_; 
v_isSharedCheck_2366_ = !lean_is_exclusive(v_code_2279_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v_code_2279_, 0);
lean_dec(v_unused_2367_);
v___x_2358_ = v_code_2279_;
v_isShared_2359_ = v_isSharedCheck_2366_;
goto v_resetjp_2357_;
}
else
{
lean_dec(v_code_2279_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2366_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 3, v_a_2344_);
v___x_2361_ = v___x_2340_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_typeName_2335_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_resultType_2336_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_discr_2337_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_a_2344_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2361_);
v___x_2363_ = v___x_2358_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
v___y_2349_ = v___x_2363_;
goto v___jp_2348_;
}
}
}
}
else
{
lean_dec(v_a_2344_);
lean_del_object(v___x_2340_);
lean_dec(v_discr_2337_);
lean_dec_ref(v_resultType_2336_);
lean_dec(v_typeName_2335_);
v___y_2349_ = v_code_2279_;
goto v___jp_2348_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_ds_2280_, v___y_2349_);
lean_dec_ref(v_ds_2280_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2350_);
v___x_2352_ = v___x_2346_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_del_object(v___x_2340_);
lean_dec_ref(v_alts_2338_);
lean_dec(v_discr_2337_);
lean_dec_ref(v_resultType_2336_);
lean_dec(v_typeName_2335_);
lean_dec_ref_known(v_code_2279_, 1);
lean_dec_ref(v_ds_2280_);
v_a_2369_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2343_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2343_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2378_; 
v_k_2378_ = lean_ctor_get(v_code_2279_, 3);
lean_inc_ref(v_k_2378_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2378_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
case 8:
{
lean_object* v_k_2379_; 
v_k_2379_ = lean_ctor_get(v_code_2279_, 3);
lean_inc_ref(v_k_2379_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2379_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
case 9:
{
lean_object* v_k_2380_; 
v_k_2380_ = lean_ctor_get(v_code_2279_, 5);
lean_inc_ref(v_k_2380_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2380_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
case 10:
{
lean_object* v_k_2381_; 
v_k_2381_ = lean_ctor_get(v_code_2279_, 2);
lean_inc_ref(v_k_2381_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2381_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
case 11:
{
lean_object* v_k_2382_; 
v_k_2382_ = lean_ctor_get(v_code_2279_, 2);
lean_inc_ref(v_k_2382_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2382_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
case 12:
{
lean_object* v_k_2383_; 
v_k_2383_ = lean_ctor_get(v_code_2279_, 3);
lean_inc_ref(v_k_2383_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2383_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
case 13:
{
lean_object* v_k_2384_; 
v_k_2384_ = lean_ctor_get(v_code_2279_, 1);
lean_inc_ref(v_k_2384_);
v_code_2288_ = v_code_2279_;
v_ds_2289_ = v_ds_2280_;
v_k_2290_ = v_k_2384_;
v___y_2291_ = v_a_2282_;
v___y_2292_ = v_a_2283_;
v___y_2293_ = v_a_2284_;
v___y_2294_ = v_a_2285_;
goto v___jp_2287_;
}
default: 
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_currentRetType_2281_);
v___x_2385_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_ds_2280_, v_code_2279_);
lean_dec_ref(v_ds_2280_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
v___jp_2287_:
{
uint8_t v___x_2295_; lean_object* v_d_2296_; lean_object* v___x_2297_; 
v___x_2295_ = 1;
v_d_2296_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2295_, v_code_2288_);
lean_dec_ref(v_code_2288_);
v___x_2297_ = lean_array_push(v_ds_2289_, v_d_2296_);
v_code_2279_ = v_k_2290_;
v_ds_2280_ = v___x_2297_;
v_a_2282_ = v___y_2291_;
v_a_2283_ = v___y_2292_;
v_a_2284_ = v___y_2293_;
v_a_2285_ = v___y_2294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2387_, lean_object* v_x_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2395_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2388_, v___x_2394_, v_resultType_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2396_, lean_object* v_i_2397_, lean_object* v_as_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2396_, v_i_2397_, v_as_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2405_, lean_object* v_ds_2406_, lean_object* v_currentRetType_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2405_, v_ds_2406_, v_currentRetType_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2414_, lean_object* v_ds_2415_, lean_object* v_decl_2416_, lean_object* v_nFields_2417_, lean_object* v_origAllocId_2418_, lean_object* v_k_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2414_, v_ds_2415_, v_decl_2416_, v_nFields_2417_, v_origAllocId_2418_, v_k_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2426_, lean_object* v_v_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
if (lean_obj_tag(v_v_2427_) == 0)
{
lean_object* v_code_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2457_; 
v_code_2433_ = lean_ctor_get(v_v_2427_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_v_2427_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2435_ = v_v_2427_;
v_isShared_2436_ = v_isSharedCheck_2457_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_code_2433_);
lean_dec(v_v_2427_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2457_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; 
lean_inc(v___y_2431_);
lean_inc_ref(v___y_2430_);
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2428_);
v___x_2437_ = lean_apply_6(v_f_2426_, v_code_2433_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2448_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2448_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2448_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v_a_2438_);
v___x_2443_ = v___x_2435_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2443_);
v___x_2445_ = v___x_2440_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_del_object(v___x_2435_);
v_a_2449_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2437_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2437_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
else
{
lean_object* v___x_2458_; 
lean_dec_ref(v_f_2426_);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_v_2427_);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2459_, lean_object* v_v_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2459_, v_v_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2467_, lean_object* v_f_2468_, lean_object* v_v_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2468_, v_v_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2476_, lean_object* v_f_2477_, lean_object* v_v_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v_pu_boxed_2484_; lean_object* v_res_2485_; 
v_pu_boxed_2484_ = lean_unbox(v_pu_2476_);
v_res_2485_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2484_, v_f_2477_, v_v_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_decl_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_toSignature_2493_; lean_object* v_type_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_toSignature_2493_ = lean_ctor_get(v_decl_2486_, 0);
lean_inc_ref(v_toSignature_2493_);
lean_dec_ref(v_decl_2486_);
v_type_2494_ = lean_ctor_get(v_toSignature_2493_, 2);
lean_inc_ref(v_type_2494_);
lean_dec_ref(v_toSignature_2493_);
v___x_2495_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2496_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2487_, v___x_2495_, v_type_2494_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_decl_2497_, lean_object* v_x_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_decl_2497_, v_x_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___f_2511_; lean_object* v___x_2512_; 
lean_inc_ref(v_decl_2505_);
v___f_2511_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2511_, 0, v_decl_2505_);
v___x_2512_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2506_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2549_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2549_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2549_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
uint8_t v_resetReuse_2517_; 
v_resetReuse_2517_ = lean_ctor_get_uint8(v_a_2513_, sizeof(void*)*4 + 2);
lean_dec(v_a_2513_);
if (v_resetReuse_2517_ == 0)
{
lean_object* v___x_2519_; 
lean_dec_ref(v___f_2511_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v_decl_2505_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_decl_2505_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
else
{
lean_object* v_toSignature_2521_; lean_object* v_value_2522_; uint8_t v_recursive_2523_; lean_object* v_inlineAttr_x3f_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2548_; 
lean_del_object(v___x_2515_);
v_toSignature_2521_ = lean_ctor_get(v_decl_2505_, 0);
v_value_2522_ = lean_ctor_get(v_decl_2505_, 1);
v_recursive_2523_ = lean_ctor_get_uint8(v_decl_2505_, sizeof(void*)*3);
v_inlineAttr_x3f_2524_ = lean_ctor_get(v_decl_2505_, 2);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_decl_2505_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2526_ = v_decl_2505_;
v_isShared_2527_ = v_isSharedCheck_2548_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_inlineAttr_x3f_2524_);
lean_inc(v_value_2522_);
lean_inc(v_toSignature_2521_);
lean_dec(v_decl_2505_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2548_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2511_, v_value_2522_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2539_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2539_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2539_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 1, v_a_2529_);
v___x_2534_ = v___x_2526_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_toSignature_2521_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_a_2529_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_inlineAttr_x3f_2524_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, sizeof(void*)*3, v_recursive_2523_);
v___x_2534_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2534_);
v___x_2536_ = v___x_2531_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2526_);
lean_dec(v_inlineAttr_x3f_2524_);
lean_dec_ref(v_toSignature_2521_);
v_a_2540_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2528_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2528_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v___f_2511_);
lean_dec_ref(v_decl_2505_);
v_a_2550_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2512_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2512_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
return v_res_2564_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2569_ = lean_unsigned_to_nat(0u);
v___x_2570_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2571_ = 2;
v___x_2572_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2573_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2572_, v___x_2571_, v___x_2570_, v___x_2569_);
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2574_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = lean_unsigned_to_nat(2743268278u);
v___x_2631_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2632_ = l_Lean_Name_num___override(v___x_2631_, v___x_2630_);
return v___x_2632_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2635_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2636_ = l_Lean_Name_str___override(v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2639_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2640_ = l_Lean_Name_str___override(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_unsigned_to_nat(2u);
v___x_2642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2643_ = l_Lean_Name_num___override(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2646_ = 1;
v___x_2647_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2648_ = l_Lean_registerTraceClass(v___x_2645_, v___x_2646_, v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2650_;
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
