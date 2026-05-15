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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.ExpandResetReuse"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ExpandResetReuse.0.Lean.Compiler.LCNF.eraseProjIncFor"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "assertion violation: n > 0 -- 0 incs should not be happening\n      "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Array_instInhabited(lean_box(0));
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
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_2915__overap_43_; lean_object* v___x_44_; 
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
v___x_2915__overap_43_ = lean_panic_fn_borrowed(v___f_42_, v_msg_5_);
lean_dec_ref(v___f_42_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
v___x_44_ = lean_apply_5(v___x_2915__overap_43_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(lean_object* v_fst_58_, lean_object* v_snd_59_, lean_object* v_fst_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0___boxed(lean_object* v_fst_71_, lean_object* v_snd_72_, lean_object* v_fst_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_71_, v_snd_72_, v_fst_73_, v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec_ref(v_x_74_);
return v_res_80_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0(void){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; 
v___x_81_ = 1;
v___x_82_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_86_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__3));
v___x_87_ = lean_unsigned_to_nat(6u);
v___x_88_ = lean_unsigned_to_nat(87u);
v___x_89_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__2));
v___x_90_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_91_ = l_mkPanicMessageWithDecl(v___x_90_, v___x_89_, v___x_88_, v___x_87_, v___x_86_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(lean_object* v_targetId_92_, lean_object* v_a_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_107_; lean_object* v_snd_127_; lean_object* v_fst_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_270_; 
v_snd_127_ = lean_ctor_get(v_a_93_, 1);
v_fst_128_ = lean_ctor_get(v_a_93_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_a_93_);
if (v_isSharedCheck_270_ == 0)
{
v___x_130_ = v_a_93_;
v_isShared_131_ = v_isSharedCheck_270_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_128_);
lean_dec(v_a_93_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_270_;
goto v_resetjp_129_;
}
v___jp_99_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___y_102_);
lean_ctor_set(v___x_103_, 1, v___y_100_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___y_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v_a_93_ = v___x_104_;
goto _start;
}
v___jp_106_:
{
if (lean_obj_tag(v___y_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_118_; 
v_a_108_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_118_ == 0)
{
v___x_110_ = v___y_107_;
v_isShared_111_ = v_isSharedCheck_118_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___y_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_118_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; 
v_a_112_ = lean_ctor_get(v_a_108_, 0);
lean_inc(v_a_112_);
lean_dec_ref(v_a_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v_a_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v_a_116_; 
lean_del_object(v___x_110_);
v_a_116_ = lean_ctor_get(v_a_108_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v_a_108_);
v_a_93_ = v_a_116_;
goto _start;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___y_107_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___y_107_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
v_resetjp_129_:
{
lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_269_; 
v_fst_132_ = lean_ctor_get(v_snd_127_, 0);
v_snd_133_ = lean_ctor_get(v_snd_127_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_snd_127_);
if (v_isSharedCheck_269_ == 0)
{
v___x_135_ = v_snd_127_;
v_isShared_136_ = v_isSharedCheck_269_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snd_133_);
lean_inc(v_fst_132_);
lean_dec(v_snd_127_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_269_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_array_get_size(v_fst_128_);
v___x_139_ = lean_nat_dec_le(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_141_; 
if (v_isShared_136_ == 0)
{
v___x_141_ = v___x_135_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_snd_133_);
v___x_141_ = v_reuseFailAlloc_146_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_141_);
v___x_143_ = v___x_130_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_fst_128_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_sub(v___x_138_, v___x_148_);
v___x_150_ = lean_array_get(v___x_147_, v_fst_128_, v___x_149_);
lean_dec(v___x_149_);
switch(lean_obj_tag(v___x_150_))
{
case 0:
{
lean_object* v_decl_151_; lean_object* v_value_152_; 
v_decl_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc_ref(v_decl_151_);
v_value_152_ = lean_ctor_get(v_decl_151_, 3);
lean_inc(v_value_152_);
switch(lean_obj_tag(v_value_152_))
{
case 8:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
lean_dec_ref(v_value_152_);
lean_dec_ref(v_decl_151_);
v___x_153_ = lean_array_pop(v_fst_128_);
v___x_154_ = lean_array_push(v_fst_132_, v___x_150_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_154_);
v___x_156_ = v___x_135_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_snd_133_);
v___x_156_ = v_reuseFailAlloc_161_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_156_);
lean_ctor_set(v___x_130_, 0, v___x_153_);
v___x_158_ = v___x_130_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
v_a_93_ = v___x_158_;
goto _start;
}
}
}
case 7:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_dec_ref(v_value_152_);
lean_dec_ref(v_decl_151_);
v___x_162_ = lean_array_pop(v_fst_128_);
v___x_163_ = lean_array_push(v_fst_132_, v___x_150_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_163_);
v___x_165_ = v___x_135_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_snd_133_);
v___x_165_ = v_reuseFailAlloc_170_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_165_);
lean_ctor_set(v___x_130_, 0, v___x_162_);
v___x_167_ = v___x_130_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_169_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
v_a_93_ = v___x_167_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_189_; 
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_190_);
v___x_172_ = v___x_150_;
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
else
{
lean_dec(v___x_150_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_fvarId_174_; lean_object* v_binderName_175_; lean_object* v_type_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_187_; 
v_fvarId_174_ = lean_ctor_get(v_decl_151_, 0);
v_binderName_175_ = lean_ctor_get(v_decl_151_, 1);
v_type_176_ = lean_ctor_get(v_decl_151_, 2);
v_isSharedCheck_187_ = !lean_is_exclusive(v_decl_151_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_decl_151_, 3);
lean_dec(v_unused_188_);
v___x_178_ = v_decl_151_;
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_type_176_);
lean_inc(v_binderName_175_);
lean_inc(v_fvarId_174_);
lean_dec(v_decl_151_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_187_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_fvarId_174_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_binderName_175_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_type_176_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_value_152_);
v___x_181_ = v_reuseFailAlloc_186_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_181_);
v___x_183_ = v___x_172_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_185_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_183_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec_ref(v___x_183_);
v___y_107_ = v___x_184_;
goto v___jp_106_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_191_; lean_object* v_n_192_; uint8_t v_check_193_; uint8_t v_persistent_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_fvarId_191_ = lean_ctor_get(v___x_150_, 0);
v_n_192_ = lean_ctor_get(v___x_150_, 1);
v_check_193_ = lean_ctor_get_uint8(v___x_150_, sizeof(void*)*2);
v_persistent_194_ = lean_ctor_get_uint8(v___x_150_, sizeof(void*)*2 + 1);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v_n_192_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v___x_150_);
lean_del_object(v___x_135_);
lean_dec(v_snd_133_);
lean_dec(v_fst_132_);
lean_del_object(v___x_130_);
lean_dec(v_fst_128_);
v___x_197_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__4);
v___x_198_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0(v___x_197_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
v___y_107_ = v___x_198_;
goto v___jp_106_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_nat_sub(v___x_138_, v___x_137_);
v___x_200_ = lean_array_get(v___x_147_, v_fst_128_, v___x_199_);
lean_dec(v___x_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_decl_201_; lean_object* v_value_202_; 
v_decl_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_ref(v_decl_201_);
v_value_202_ = lean_ctor_get(v_decl_201_, 3);
lean_inc(v_value_202_);
if (lean_obj_tag(v_value_202_) == 6)
{
lean_object* v_fvarId_203_; lean_object* v_i_204_; lean_object* v_var_205_; uint8_t v___y_207_; uint8_t v___x_245_; 
v_fvarId_203_ = lean_ctor_get(v_decl_201_, 0);
lean_inc(v_fvarId_203_);
lean_dec_ref(v_decl_201_);
v_i_204_ = lean_ctor_get(v_value_202_, 0);
lean_inc(v_i_204_);
v_var_205_ = lean_ctor_get(v_value_202_, 1);
lean_inc(v_var_205_);
lean_dec_ref(v_value_202_);
v___x_245_ = l_Lean_instBEqFVarId_beq(v_fvarId_203_, v_fvarId_191_);
lean_dec(v_fvarId_203_);
if (v___x_245_ == 0)
{
lean_dec(v_var_205_);
v___y_207_ = v___x_245_;
goto v___jp_206_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = l_Lean_instBEqFVarId_beq(v_targetId_92_, v_var_205_);
lean_dec(v_var_205_);
v___y_207_ = v___x_246_;
goto v___jp_206_;
}
v___jp_206_:
{
if (v___y_207_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v_i_204_);
lean_dec_ref(v___x_200_);
lean_dec_ref(v___x_150_);
if (v_isShared_136_ == 0)
{
v___x_209_ = v___x_135_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_snd_133_);
v___x_209_ = v_reuseFailAlloc_214_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_209_);
v___x_211_ = v___x_130_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_fst_128_);
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
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_array_get_borrowed(v___x_215_, v_snd_133_, v_i_204_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_231_; 
lean_inc(v_n_192_);
lean_inc(v_fvarId_191_);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_232_ = lean_ctor_get(v___x_150_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_233_);
v___x_218_ = v___x_150_;
v_isShared_219_ = v_isSharedCheck_231_;
goto v_resetjp_217_;
}
else
{
lean_dec(v___x_150_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_231_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_220_ = lean_array_pop(v_fst_128_);
v___x_221_ = lean_array_pop(v___x_220_);
lean_inc(v_fvarId_191_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_fvarId_191_);
v___x_223_ = lean_array_set(v_snd_133_, v_i_204_, v___x_222_);
lean_dec(v_i_204_);
v___x_224_ = lean_array_push(v_fst_132_, v___x_200_);
v___x_225_ = lean_nat_dec_eq(v_n_192_, v___x_148_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_nat_sub(v_n_192_, v___x_148_);
lean_dec(v_n_192_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_226_);
v___x_228_ = v___x_218_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_fvarId_191_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_226_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*2, v_check_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*2 + 1, v_persistent_194_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_array_push(v___x_224_, v___x_228_);
v___y_100_ = v___x_223_;
v___y_101_ = v___x_221_;
v___y_102_ = v___x_229_;
goto v___jp_99_;
}
}
else
{
lean_del_object(v___x_218_);
lean_dec(v_n_192_);
lean_dec(v_fvarId_191_);
v___y_100_ = v___x_223_;
v___y_101_ = v___x_221_;
v___y_102_ = v___x_224_;
goto v___jp_99_;
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v_i_204_);
v___x_234_ = lean_array_push(v_fst_132_, v___x_150_);
v___x_235_ = lean_array_push(v___x_234_, v___x_200_);
v___x_236_ = lean_array_pop(v_fst_128_);
v___x_237_ = lean_array_pop(v___x_236_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_235_);
v___x_239_ = v___x_135_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_snd_133_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_239_);
lean_ctor_set(v___x_130_, 0, v___x_237_);
v___x_241_ = v___x_130_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v_a_93_ = v___x_241_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v___x_150_);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_200_, 0);
lean_dec(v_unused_266_);
v___x_248_ = v___x_200_;
v_isShared_249_ = v_isSharedCheck_265_;
goto v_resetjp_247_;
}
else
{
lean_dec(v___x_200_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_265_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_fvarId_250_; lean_object* v_binderName_251_; lean_object* v_type_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_263_; 
v_fvarId_250_ = lean_ctor_get(v_decl_201_, 0);
v_binderName_251_ = lean_ctor_get(v_decl_201_, 1);
v_type_252_ = lean_ctor_get(v_decl_201_, 2);
v_isSharedCheck_263_ = !lean_is_exclusive(v_decl_201_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; 
v_unused_264_ = lean_ctor_get(v_decl_201_, 3);
lean_dec(v_unused_264_);
v___x_254_ = v_decl_201_;
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_type_252_);
lean_inc(v_binderName_251_);
lean_inc(v_fvarId_250_);
lean_dec(v_decl_201_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fvarId_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_binderName_251_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_type_252_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_value_202_);
v___x_257_ = v_reuseFailAlloc_262_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_257_);
v___x_259_ = v___x_248_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_259_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec_ref(v___x_259_);
v___y_107_ = v___x_260_;
goto v___jp_106_;
}
}
}
}
}
}
else
{
lean_object* v___x_267_; 
lean_dec_ref(v___x_150_);
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v___x_267_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_200_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___x_200_);
v___y_107_ = v___x_267_;
goto v___jp_106_;
}
}
}
default: 
{
lean_object* v___x_268_; 
lean_del_object(v___x_135_);
lean_del_object(v___x_130_);
v___x_268_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___lam__0(v_fst_132_, v_snd_133_, v_fst_128_, v___x_150_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___x_150_);
v___y_107_ = v___x_268_;
goto v___jp_106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___boxed(lean_object* v_targetId_271_, lean_object* v_a_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_271_, v_a_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v_targetId_271_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(lean_object* v_nFields_281_, lean_object* v_targetId_282_, lean_object* v_ds_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_keep_289_; lean_object* v___x_290_; lean_object* v_mask_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_keep_289_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_290_ = lean_box(0);
v_mask_291_ = lean_mk_array(v_nFields_281_, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_keep_289_);
lean_ctor_set(v___x_292_, 1, v_mask_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_ds_283_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_282_, v___x_293_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_315_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_315_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_315_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_315_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_snd_299_; lean_object* v_fst_300_; lean_object* v_fst_301_; lean_object* v_snd_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v_snd_299_ = lean_ctor_get(v_a_295_, 1);
lean_inc(v_snd_299_);
v_fst_300_ = lean_ctor_get(v_a_295_, 0);
lean_inc(v_fst_300_);
lean_dec(v_a_295_);
v_fst_301_ = lean_ctor_get(v_snd_299_, 0);
v_snd_302_ = lean_ctor_get(v_snd_299_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_snd_299_);
if (v_isSharedCheck_314_ == 0)
{
v___x_304_ = v_snd_299_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_snd_302_);
lean_inc(v_fst_301_);
lean_dec(v_snd_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = l_Array_reverse___redArg(v_fst_301_);
v___x_307_ = l_Array_append___redArg(v_fst_300_, v___x_306_);
lean_dec_ref(v___x_306_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_snd_302_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_309_);
v___x_311_ = v___x_297_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
v_a_316_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_294_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_294_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___boxed(lean_object* v_nFields_324_, lean_object* v_targetId_325_, lean_object* v_ds_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_324_, v_targetId_325_, v_ds_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_targetId_325_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(lean_object* v_targetId_333_, lean_object* v_inst_334_, lean_object* v_a_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg(v_targetId_333_, v_a_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___boxed(lean_object* v_targetId_342_, lean_object* v_inst_343_, lean_object* v_a_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1(v_targetId_342_, v_inst_343_, v_a_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v_targetId_342_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(lean_object* v_discr_367_, lean_object* v_discrType_368_, lean_object* v_resultType_369_, lean_object* v_t_370_, lean_object* v_e_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_373_ = l_Lean_Expr_getAppFn(v_discrType_368_);
v___x_374_ = l_Lean_Expr_constName_x21(v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__3));
v___x_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_e_371_);
v___x_377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___closed__6));
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_t_370_);
v___x_379_ = lean_unsigned_to_nat(2u);
v___x_380_ = lean_mk_empty_array_with_capacity(v___x_379_);
v___x_381_ = lean_array_push(v___x_380_, v___x_376_);
v___x_382_ = lean_array_push(v___x_381_, v___x_378_);
v___x_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_383_, 0, v___x_374_);
lean_ctor_set(v___x_383_, 1, v_resultType_369_);
lean_ctor_set(v___x_383_, 2, v_discr_367_);
lean_ctor_set(v___x_383_, 3, v___x_382_);
v___x_384_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg___boxed(lean_object* v_discr_386_, lean_object* v_discrType_387_, lean_object* v_resultType_388_, lean_object* v_t_389_, lean_object* v_e_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_386_, v_discrType_387_, v_resultType_388_, v_t_389_, v_e_390_);
lean_dec_ref(v_discrType_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(lean_object* v_discr_393_, lean_object* v_discrType_394_, lean_object* v_resultType_395_, lean_object* v_t_396_, lean_object* v_e_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_discr_393_, v_discrType_394_, v_resultType_395_, v_t_396_, v_e_397_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___boxed(lean_object* v_discr_404_, lean_object* v_discrType_405_, lean_object* v_resultType_406_, lean_object* v_t_407_, lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf(v_discr_404_, v_discrType_405_, v_resultType_406_, v_t_407_, v_e_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_discrType_405_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(lean_object* v_msg_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__0);
v___x_417_ = lean_panic_fn_borrowed(v___x_416_, v_msg_415_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_421_ = lean_unsigned_to_nat(11u);
v___x_422_ = lean_unsigned_to_nat(138u);
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__0));
v___x_424_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_425_ = l_mkPanicMessageWithDecl(v___x_424_, v___x_423_, v___x_422_, v___x_421_, v___x_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(lean_object* v_targetId_426_, size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_430_ == 0)
{
lean_dec(v_targetId_426_);
return v_bs_429_;
}
else
{
lean_object* v_v_431_; lean_object* v___x_432_; lean_object* v_bs_x27_433_; lean_object* v___y_435_; 
v_v_431_ = lean_array_uget(v_bs_429_, v_i_428_);
v___x_432_ = lean_unsigned_to_nat(0u);
v_bs_x27_433_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_432_);
switch(lean_obj_tag(v_v_431_))
{
case 3:
{
lean_object* v_i_440_; lean_object* v_y_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_i_440_ = lean_ctor_get(v_v_431_, 1);
v_y_441_ = lean_ctor_get(v_v_431_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_v_431_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v_v_431_, 0);
lean_dec(v_unused_449_);
v___x_443_ = v_v_431_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_y_441_);
lean_inc(v_i_440_);
lean_dec(v_v_431_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
lean_inc(v_targetId_426_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_targetId_426_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_targetId_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_i_440_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_y_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v___y_435_ = v___x_446_;
goto v___jp_434_;
}
}
}
case 5:
{
lean_object* v_i_450_; lean_object* v_offset_451_; lean_object* v_y_452_; lean_object* v_ty_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_i_450_ = lean_ctor_get(v_v_431_, 1);
v_offset_451_ = lean_ctor_get(v_v_431_, 2);
v_y_452_ = lean_ctor_get(v_v_431_, 3);
v_ty_453_ = lean_ctor_get(v_v_431_, 4);
v_isSharedCheck_460_ = !lean_is_exclusive(v_v_431_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_v_431_, 0);
lean_dec(v_unused_461_);
v___x_455_ = v_v_431_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_ty_453_);
lean_inc(v_y_452_);
lean_inc(v_offset_451_);
lean_inc(v_i_450_);
lean_dec(v_v_431_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
lean_inc(v_targetId_426_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_targetId_426_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_targetId_426_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_i_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_offset_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_y_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_ty_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
v___y_435_ = v___x_458_;
goto v___jp_434_;
}
}
}
case 4:
{
lean_object* v_i_462_; lean_object* v_y_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_i_462_ = lean_ctor_get(v_v_431_, 1);
v_y_463_ = lean_ctor_get(v_v_431_, 2);
v_isSharedCheck_470_ = !lean_is_exclusive(v_v_431_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_v_431_, 0);
lean_dec(v_unused_471_);
v___x_465_ = v_v_431_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_y_463_);
lean_inc(v_i_462_);
lean_dec(v_v_431_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
lean_inc(v_targetId_426_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v_targetId_426_);
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_targetId_426_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_i_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_y_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v___y_435_ = v___x_468_;
goto v___jp_434_;
}
}
}
default: 
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v_v_431_);
v___x_472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__2);
v___x_473_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__0(v___x_472_);
v___y_435_ = v___x_473_;
goto v___jp_434_;
}
}
v___jp_434_:
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_428_, v___x_436_);
v___x_438_ = lean_array_uset(v_bs_x27_433_, v_i_428_, v___y_435_);
v_i_428_ = v___x_437_;
v_bs_429_ = v___x_438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___boxed(lean_object* v_targetId_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_bs_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_479_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_474_, v_sz_boxed_478_, v_i_boxed_479_, v_bs_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(lean_object* v_targetId_481_, lean_object* v_sets_482_){
_start:
{
size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_sz_484_ = lean_array_size(v_sets_482_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1(v_targetId_481_, v_sz_484_, v___x_485_, v_sets_482_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg___boxed(lean_object* v_targetId_488_, lean_object* v_sets_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_488_, v_sets_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(lean_object* v_targetId_492_, lean_object* v_sets_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_targetId_492_, v_sets_493_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___boxed(lean_object* v_targetId_500_, lean_object* v_sets_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets(v_targetId_500_, v_sets_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(lean_object* v_fvarId_508_, lean_object* v_i_509_, lean_object* v_y_510_, lean_object* v_a_511_){
_start:
{
if (lean_obj_tag(v_y_510_) == 0)
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = 0;
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v_fvarId_516_; uint8_t v___x_517_; lean_object* v___x_518_; 
v_fvarId_516_ = lean_ctor_get(v_y_510_, 0);
v___x_517_ = 1;
v___x_518_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_517_, v_fvarId_516_, v_a_511_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_546_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_546_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_546_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_546_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
if (lean_obj_tag(v_a_519_) == 1)
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v_a_519_, 0);
lean_inc(v_val_523_);
lean_dec_ref(v_a_519_);
if (lean_obj_tag(v_val_523_) == 6)
{
lean_object* v_i_524_; lean_object* v_var_525_; uint8_t v___x_526_; 
v_i_524_ = lean_ctor_get(v_val_523_, 0);
lean_inc(v_i_524_);
v_var_525_ = lean_ctor_get(v_val_523_, 1);
lean_inc(v_var_525_);
lean_dec_ref(v_val_523_);
v___x_526_ = lean_nat_dec_eq(v_i_509_, v_i_524_);
lean_dec(v_i_524_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec(v_var_525_);
v___x_527_ = lean_box(v___x_526_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_527_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = l_Lean_instBEqFVarId_beq(v_fvarId_508_, v_var_525_);
lean_dec(v_var_525_);
v___x_532_ = lean_box(v___x_531_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_532_);
v___x_534_ = v___x_521_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_val_523_);
v___x_536_ = 0;
v___x_537_ = lean_box(v___x_536_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_537_);
v___x_539_ = v___x_521_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_dec(v_a_519_);
v___x_541_ = 0;
v___x_542_ = lean_box(v___x_541_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_542_);
v___x_544_ = v___x_521_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_518_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_518_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg___boxed(lean_object* v_fvarId_555_, lean_object* v_i_556_, lean_object* v_y_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_555_, v_i_556_, v_y_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec(v_y_557_);
lean_dec(v_i_556_);
lean_dec(v_fvarId_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(lean_object* v_fvarId_561_, lean_object* v_i_562_, lean_object* v_y_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_fvarId_561_, v_i_562_, v_y_563_, v_a_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___boxed(lean_object* v_fvarId_570_, lean_object* v_i_571_, lean_object* v_y_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset(v_fvarId_570_, v_i_571_, v_y_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_y_572_);
lean_dec(v_i_571_);
lean_dec(v_fvarId_570_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(lean_object* v_fvarId_579_, lean_object* v_i_580_, lean_object* v_y_581_, lean_object* v_a_582_){
_start:
{
uint8_t v___x_584_; lean_object* v___x_585_; 
v___x_584_ = 1;
v___x_585_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_584_, v_y_581_, v_a_582_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_613_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_613_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_613_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_613_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
if (lean_obj_tag(v_a_586_) == 1)
{
lean_object* v_val_590_; 
v_val_590_ = lean_ctor_get(v_a_586_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v_a_586_);
if (lean_obj_tag(v_val_590_) == 7)
{
lean_object* v_i_591_; lean_object* v_var_592_; uint8_t v___x_593_; 
v_i_591_ = lean_ctor_get(v_val_590_, 0);
lean_inc(v_i_591_);
v_var_592_ = lean_ctor_get(v_val_590_, 1);
lean_inc(v_var_592_);
lean_dec_ref(v_val_590_);
v___x_593_ = lean_nat_dec_eq(v_i_580_, v_i_591_);
lean_dec(v_i_591_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
lean_dec(v_var_592_);
v___x_594_ = lean_box(v___x_593_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_594_);
v___x_596_ = v___x_588_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = l_Lean_instBEqFVarId_beq(v_fvarId_579_, v_var_592_);
lean_dec(v_var_592_);
v___x_599_ = lean_box(v___x_598_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_599_);
v___x_601_ = v___x_588_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec(v_val_590_);
v___x_603_ = 0;
v___x_604_ = lean_box(v___x_603_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_604_);
v___x_606_ = v___x_588_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_a_586_);
v___x_608_ = 0;
v___x_609_ = lean_box(v___x_608_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_609_);
v___x_611_ = v___x_588_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_585_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_585_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg___boxed(lean_object* v_fvarId_622_, lean_object* v_i_623_, lean_object* v_y_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_622_, v_i_623_, v_y_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec(v_y_624_);
lean_dec(v_i_623_);
lean_dec(v_fvarId_622_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(lean_object* v_fvarId_628_, lean_object* v_i_629_, lean_object* v_y_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_fvarId_628_, v_i_629_, v_y_630_, v_a_632_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___boxed(lean_object* v_fvarId_637_, lean_object* v_i_638_, lean_object* v_y_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset(v_fvarId_637_, v_i_638_, v_y_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_y_639_);
lean_dec(v_i_638_);
lean_dec(v_fvarId_637_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(lean_object* v_fvarId_646_, lean_object* v_i_647_, lean_object* v_offset_648_, lean_object* v_y_649_, lean_object* v_a_650_){
_start:
{
uint8_t v___x_652_; lean_object* v___x_653_; 
v___x_652_ = 1;
v___x_653_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_652_, v_y_649_, v_a_650_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_685_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_685_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
if (lean_obj_tag(v_a_654_) == 1)
{
lean_object* v_val_658_; 
v_val_658_ = lean_ctor_get(v_a_654_, 0);
lean_inc(v_val_658_);
lean_dec_ref(v_a_654_);
if (lean_obj_tag(v_val_658_) == 8)
{
lean_object* v_n_659_; lean_object* v_offset_660_; lean_object* v_var_661_; uint8_t v___y_663_; uint8_t v___x_673_; 
v_n_659_ = lean_ctor_get(v_val_658_, 0);
lean_inc(v_n_659_);
v_offset_660_ = lean_ctor_get(v_val_658_, 1);
lean_inc(v_offset_660_);
v_var_661_ = lean_ctor_get(v_val_658_, 2);
lean_inc(v_var_661_);
lean_dec_ref(v_val_658_);
v___x_673_ = lean_nat_dec_eq(v_i_647_, v_n_659_);
lean_dec(v_n_659_);
if (v___x_673_ == 0)
{
lean_dec(v_offset_660_);
v___y_663_ = v___x_673_;
goto v___jp_662_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_eq(v_offset_648_, v_offset_660_);
lean_dec(v_offset_660_);
v___y_663_ = v___x_674_;
goto v___jp_662_;
}
v___jp_662_:
{
if (v___y_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_dec(v_var_661_);
v___x_664_ = lean_box(v___y_663_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_664_);
v___x_666_ = v___x_656_;
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
v___x_668_ = l_Lean_instBEqFVarId_beq(v_fvarId_646_, v_var_661_);
lean_dec(v_var_661_);
v___x_669_ = lean_box(v___x_668_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_669_);
v___x_671_ = v___x_656_;
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
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec(v_val_658_);
v___x_675_ = 0;
v___x_676_ = lean_box(v___x_675_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_676_);
v___x_678_ = v___x_656_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
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
else
{
uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_dec(v_a_654_);
v___x_680_ = 0;
v___x_681_ = lean_box(v___x_680_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_681_);
v___x_683_ = v___x_656_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
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
v_a_686_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_653_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_653_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg___boxed(lean_object* v_fvarId_694_, lean_object* v_i_695_, lean_object* v_offset_696_, lean_object* v_y_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_694_, v_i_695_, v_offset_696_, v_y_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec(v_y_697_);
lean_dec(v_offset_696_);
lean_dec(v_i_695_);
lean_dec(v_fvarId_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(lean_object* v_fvarId_701_, lean_object* v_i_702_, lean_object* v_offset_703_, lean_object* v_y_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_fvarId_701_, v_i_702_, v_offset_703_, v_y_704_, v_a_706_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___boxed(lean_object* v_fvarId_711_, lean_object* v_i_712_, lean_object* v_offset_713_, lean_object* v_y_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset(v_fvarId_711_, v_i_712_, v_offset_713_, v_y_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_y_714_);
lean_dec(v_offset_713_);
lean_dec(v_i_712_);
lean_dec(v_fvarId_711_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_toApplicative_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_763_; 
v___x_727_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_728_ = l_StateRefT_x27_instMonad___redArg(v___x_727_);
v_toApplicative_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_728_, 1);
lean_dec(v_unused_764_);
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_763_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_toApplicative_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_763_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_toFunctor_733_; lean_object* v_toSeq_734_; lean_object* v_toSeqLeft_735_; lean_object* v_toSeqRight_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_761_; 
v_toFunctor_733_ = lean_ctor_get(v_toApplicative_729_, 0);
v_toSeq_734_ = lean_ctor_get(v_toApplicative_729_, 2);
v_toSeqLeft_735_ = lean_ctor_get(v_toApplicative_729_, 3);
v_toSeqRight_736_ = lean_ctor_get(v_toApplicative_729_, 4);
v_isSharedCheck_761_ = !lean_is_exclusive(v_toApplicative_729_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_toApplicative_729_, 1);
lean_dec(v_unused_762_);
v___x_738_ = v_toApplicative_729_;
v_isShared_739_ = v_isSharedCheck_761_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_toSeqRight_736_);
lean_inc(v_toSeqLeft_735_);
lean_inc(v_toSeq_734_);
lean_inc(v_toFunctor_733_);
lean_dec(v_toApplicative_729_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_761_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_749_; 
v___f_740_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_741_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_733_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_742_, 0, v_toFunctor_733_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_743_, 0, v_toFunctor_733_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___f_742_);
lean_ctor_set(v___x_744_, 1, v___f_743_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_745_, 0, v_toSeqRight_736_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_746_, 0, v_toSeqLeft_735_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_747_, 0, v_toSeq_734_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___f_745_);
lean_ctor_set(v___x_738_, 3, v___f_746_);
lean_ctor_set(v___x_738_, 2, v___f_747_);
lean_ctor_set(v___x_738_, 1, v___f_740_);
lean_ctor_set(v___x_738_, 0, v___x_744_);
v___x_749_ = v___x_738_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___f_740_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v___f_747_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v___f_746_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v___f_745_);
v___x_749_ = v_reuseFailAlloc_760_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_751_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___f_741_);
lean_ctor_set(v___x_731_, 0, v___x_749_);
v___x_751_ = v___x_731_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___f_741_);
v___x_751_ = v_reuseFailAlloc_759_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v___x_994__overap_757_; lean_object* v___x_758_; 
v___x_752_ = l_StateRefT_x27_instMonad___redArg(v___x_751_);
v___x_753_ = 0;
v___x_754_ = lean_box(v___x_753_);
v___x_755_ = l_instInhabitedOfMonad___redArg(v___x_752_, v___x_754_);
v___f_756_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_756_, 0, v___x_755_);
v___x_994__overap_757_ = lean_panic_fn_borrowed(v___f_756_, v_msg_721_);
lean_dec_ref(v___f_756_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
v___x_758_ = lean_apply_5(v___x_994__overap_757_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, lean_box(0));
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0___boxed(lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v_msg_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets_spec__1___closed__1));
v___x_774_ = lean_unsigned_to_nat(13u);
v___x_775_ = lean_unsigned_to_nat(174u);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__0));
v___x_777_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_778_ = l_mkPanicMessageWithDecl(v___x_777_, v___x_776_, v___x_775_, v___x_774_, v___x_773_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(lean_object* v_selfId_779_, lean_object* v_as_780_, size_t v_sz_781_, size_t v_i_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_a_790_; uint8_t v___x_794_; 
v___x_794_ = lean_usize_dec_lt(v_i_782_, v_sz_781_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_b_783_);
return v___x_795_;
}
else
{
lean_object* v_fst_796_; lean_object* v_snd_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_834_; 
v_fst_796_ = lean_ctor_get(v_b_783_, 0);
v_snd_797_ = lean_ctor_get(v_b_783_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_b_783_);
if (v_isSharedCheck_834_ == 0)
{
v___x_799_ = v_b_783_;
v_isShared_800_ = v_isSharedCheck_834_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snd_797_);
lean_inc(v_fst_796_);
lean_dec(v_b_783_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_834_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_a_801_; lean_object* v___y_803_; 
v_a_801_ = lean_array_uget_borrowed(v_as_780_, v_i_782_);
switch(lean_obj_tag(v_a_801_))
{
case 3:
{
lean_object* v_i_822_; lean_object* v_y_823_; lean_object* v___x_824_; 
v_i_822_ = lean_ctor_get(v_a_801_, 1);
v_y_823_ = lean_ctor_get(v_a_801_, 2);
v___x_824_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_selfId_779_, v_i_822_, v_y_823_, v___y_785_);
v___y_803_ = v___x_824_;
goto v___jp_802_;
}
case 4:
{
lean_object* v_i_825_; lean_object* v_y_826_; lean_object* v___x_827_; 
v_i_825_ = lean_ctor_get(v_a_801_, 1);
v_y_826_ = lean_ctor_get(v_a_801_, 2);
v___x_827_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfUset___redArg(v_selfId_779_, v_i_825_, v_y_826_, v___y_785_);
v___y_803_ = v___x_827_;
goto v___jp_802_;
}
case 5:
{
lean_object* v_i_828_; lean_object* v_offset_829_; lean_object* v_y_830_; lean_object* v___x_831_; 
v_i_828_ = lean_ctor_get(v_a_801_, 1);
v_offset_829_ = lean_ctor_get(v_a_801_, 2);
v_y_830_ = lean_ctor_get(v_a_801_, 3);
v___x_831_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfSset___redArg(v_selfId_779_, v_i_828_, v_offset_829_, v_y_830_, v___y_785_);
v___y_803_ = v___x_831_;
goto v___jp_802_;
}
default: 
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___closed__1);
v___x_833_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__0(v___x_832_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
v___y_803_ = v___x_833_;
goto v___jp_802_;
}
}
v___jp_802_:
{
if (lean_obj_tag(v___y_803_) == 0)
{
lean_object* v_a_804_; uint8_t v___x_805_; 
v_a_804_ = lean_ctor_get(v___y_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___y_803_);
v___x_805_ = lean_unbox(v_a_804_);
lean_dec(v_a_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_inc(v_a_801_);
v___x_806_ = lean_array_push(v_fst_796_, v_a_801_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_snd_797_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
v_a_790_ = v___x_808_;
goto v___jp_789_;
}
}
else
{
lean_object* v___x_810_; lean_object* v___x_812_; 
lean_inc(v_a_801_);
v___x_810_ = lean_array_push(v_snd_797_, v_a_801_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_810_);
v___x_812_ = v___x_799_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_790_ = v___x_812_;
goto v___jp_789_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_del_object(v___x_799_);
lean_dec(v_snd_797_);
lean_dec(v_fst_796_);
v_a_814_ = lean_ctor_get(v___y_803_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___y_803_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___y_803_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___y_803_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
v___jp_789_:
{
size_t v___x_791_; size_t v___x_792_; 
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_782_, v___x_791_);
v_i_782_ = v___x_792_;
v_b_783_ = v_a_790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1___boxed(lean_object* v_selfId_835_, lean_object* v_as_836_, lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_b_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
size_t v_sz_boxed_845_; size_t v_i_boxed_846_; lean_object* v_res_847_; 
v_sz_boxed_845_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_846_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_835_, v_as_836_, v_sz_boxed_845_, v_i_boxed_846_, v_b_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_as_836_);
lean_dec(v_selfId_835_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(lean_object* v_selfId_850_, lean_object* v_sets_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; size_t v_sz_858_; size_t v___x_859_; lean_object* v___x_860_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___closed__0));
v_sz_858_ = lean_array_size(v_sets_851_);
v___x_859_ = ((size_t)0ULL);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets_spec__1(v_selfId_850_, v_sets_851_, v_sz_858_, v___x_859_, v___x_857_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_877_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_877_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_877_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_877_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v_fst_865_ = lean_ctor_get(v_a_861_, 0);
v_snd_866_ = lean_ctor_get(v_a_861_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_a_861_);
if (v_isSharedCheck_876_ == 0)
{
v___x_868_ = v_a_861_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_inc(v_fst_865_);
lean_dec(v_a_861_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_fst_865_);
lean_ctor_set(v___x_868_, 0, v_snd_866_);
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_snd_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_fst_865_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_871_);
v___x_873_ = v___x_863_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
else
{
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets___boxed(lean_object* v_selfId_878_, lean_object* v_sets_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_selfId_878_, v_sets_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec_ref(v_sets_879_);
lean_dec(v_selfId_878_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(lean_object* v_target_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_snd_889_; 
v_snd_889_ = lean_ctor_get(v_a_887_, 1);
lean_inc(v_snd_889_);
switch(lean_obj_tag(v_snd_889_))
{
case 7:
{
lean_object* v_fst_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_908_; 
v_fst_890_ = lean_ctor_get(v_a_887_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_a_887_, 1);
lean_dec(v_unused_909_);
v___x_892_ = v_a_887_;
v_isShared_893_ = v_isSharedCheck_908_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_fst_890_);
lean_dec(v_a_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_908_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_fvarId_894_; lean_object* v_k_895_; uint8_t v___x_896_; 
v_fvarId_894_ = lean_ctor_get(v_snd_889_, 0);
v_k_895_ = lean_ctor_get(v_snd_889_, 3);
v___x_896_ = l_Lean_instBEqFVarId_beq(v_target_886_, v_fvarId_894_);
if (v___x_896_ == 0)
{
lean_object* v___x_898_; 
if (v_isShared_893_ == 0)
{
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_fst_890_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_snd_889_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
else
{
uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
lean_inc_ref(v_k_895_);
v___x_901_ = 1;
v___x_902_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_901_, v_snd_889_);
lean_dec_ref(v_snd_889_);
v___x_903_ = lean_array_push(v_fst_890_, v___x_902_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_k_895_);
lean_ctor_set(v___x_892_, 0, v___x_903_);
v___x_905_ = v___x_892_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_895_);
v___x_905_ = v_reuseFailAlloc_907_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
v_a_887_ = v___x_905_;
goto _start;
}
}
}
}
case 9:
{
lean_object* v_fst_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_928_; 
v_fst_910_ = lean_ctor_get(v_a_887_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_a_887_, 1);
lean_dec(v_unused_929_);
v___x_912_ = v_a_887_;
v_isShared_913_ = v_isSharedCheck_928_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_fst_910_);
lean_dec(v_a_887_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_928_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fvarId_914_; lean_object* v_k_915_; uint8_t v___x_916_; 
v_fvarId_914_ = lean_ctor_get(v_snd_889_, 0);
v_k_915_ = lean_ctor_get(v_snd_889_, 5);
v___x_916_ = l_Lean_instBEqFVarId_beq(v_target_886_, v_fvarId_914_);
if (v___x_916_ == 0)
{
lean_object* v___x_918_; 
if (v_isShared_913_ == 0)
{
v___x_918_ = v___x_912_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_889_);
v___x_918_ = v_reuseFailAlloc_920_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; 
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
else
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
lean_inc_ref(v_k_915_);
v___x_921_ = 1;
v___x_922_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_921_, v_snd_889_);
lean_dec_ref(v_snd_889_);
v___x_923_ = lean_array_push(v_fst_910_, v___x_922_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_k_915_);
lean_ctor_set(v___x_912_, 0, v___x_923_);
v___x_925_ = v___x_912_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_915_);
v___x_925_ = v_reuseFailAlloc_927_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v_a_887_ = v___x_925_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_fst_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_948_; 
v_fst_930_ = lean_ctor_get(v_a_887_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_a_887_, 1);
lean_dec(v_unused_949_);
v___x_932_ = v_a_887_;
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_fst_930_);
lean_dec(v_a_887_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_fvarId_934_; lean_object* v_k_935_; uint8_t v___x_936_; 
v_fvarId_934_ = lean_ctor_get(v_snd_889_, 0);
v_k_935_ = lean_ctor_get(v_snd_889_, 3);
v___x_936_ = l_Lean_instBEqFVarId_beq(v_target_886_, v_fvarId_934_);
if (v___x_936_ == 0)
{
lean_object* v___x_938_; 
if (v_isShared_933_ == 0)
{
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_fst_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_snd_889_);
v___x_938_ = v_reuseFailAlloc_940_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
else
{
uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_inc_ref(v_k_935_);
v___x_941_ = 1;
v___x_942_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_941_, v_snd_889_);
lean_dec_ref(v_snd_889_);
v___x_943_ = lean_array_push(v_fst_930_, v___x_942_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v_k_935_);
lean_ctor_set(v___x_932_, 0, v___x_943_);
v___x_945_ = v___x_932_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_k_935_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v_a_887_ = v___x_945_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_fst_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_958_; 
v_fst_950_ = lean_ctor_get(v_a_887_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_a_887_, 1);
lean_dec(v_unused_959_);
v___x_952_ = v_a_887_;
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_fst_950_);
lean_dec(v_a_887_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_snd_889_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
return v___x_956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg___boxed(lean_object* v_target_960_, lean_object* v_a_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_960_, v_a_961_);
lean_dec(v_target_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(lean_object* v_target_964_, lean_object* v_k_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_sets_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_sets_971_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_sets_971_);
lean_ctor_set(v___x_972_, 1, v_k_965_);
v___x_973_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_964_, v___x_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_990_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_990_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_990_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_990_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_fst_978_; lean_object* v_snd_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_989_; 
v_fst_978_ = lean_ctor_get(v_a_974_, 0);
v_snd_979_ = lean_ctor_get(v_a_974_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_989_ == 0)
{
v___x_981_ = v_a_974_;
v_isShared_982_ = v_isSharedCheck_989_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_snd_979_);
lean_inc(v_fst_978_);
lean_dec(v_a_974_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_989_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_fst_978_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_snd_979_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_984_);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
else
{
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets___boxed(lean_object* v_target_991_, lean_object* v_k_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_target_991_, v_k_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_target_991_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(lean_object* v_target_999_, lean_object* v_inst_1000_, lean_object* v_a_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___redArg(v_target_999_, v_a_1001_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0___boxed(lean_object* v_target_1008_, lean_object* v_inst_1009_, lean_object* v_a_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets_spec__0(v_target_1008_, v_inst_1009_, v_a_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v_target_1008_);
return v_res_1016_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__3));
v___x_1025_ = l_Lean_Expr_const___override(v___x_1024_, v___x_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(lean_object* v_upperBound_1026_, lean_object* v_mask_1027_, lean_object* v_origAllocId_1028_, lean_object* v_a_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_a_1037_; uint8_t v___x_1041_; 
v___x_1041_ = lean_nat_dec_lt(v_a_1029_, v_upperBound_1026_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec(v_a_1029_);
lean_dec(v_origAllocId_1028_);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_b_1030_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_array_fget_borrowed(v_mask_1027_, v_a_1029_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__1));
v___x_1045_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1044_, v___y_1032_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = 1;
v___x_1048_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_origAllocId_1028_);
lean_inc(v_a_1029_);
v___x_1049_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_a_1029_);
lean_ctor_set(v___x_1049_, 1, v_origAllocId_1028_);
v___x_1050_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1047_, v_a_1046_, v___x_1048_, v___x_1049_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v_fvarId_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref(v___x_1050_);
v_fvarId_1052_ = lean_ctor_get(v_a_1051_, 0);
v___x_1053_ = 0;
v___x_1054_ = lean_unsigned_to_nat(1u);
lean_inc(v_fvarId_1052_);
v___x_1055_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v___x_1055_, 0, v_fvarId_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
lean_ctor_set(v___x_1055_, 2, v_b_1030_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*3, v___x_1041_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*3 + 1, v___x_1053_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1051_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v_a_1037_ = v___x_1056_;
goto v___jp_1036_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_b_1030_);
lean_dec(v_a_1029_);
lean_dec(v_origAllocId_1028_);
v_a_1057_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1050_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1050_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_b_1030_);
lean_dec(v_a_1029_);
lean_dec(v_origAllocId_1028_);
v_a_1065_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1045_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1045_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
v_a_1037_ = v_b_1030_;
goto v___jp_1036_;
}
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_unsigned_to_nat(1u);
v___x_1039_ = lean_nat_add(v_a_1029_, v___x_1038_);
lean_dec(v_a_1029_);
v_a_1029_ = v___x_1039_;
v_b_1030_ = v_a_1037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___boxed(lean_object* v_upperBound_1073_, lean_object* v_mask_1074_, lean_object* v_origAllocId_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1073_, v_mask_1074_, v_origAllocId_1075_, v_a_1076_, v_b_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v_mask_1074_);
lean_dec(v_upperBound_1073_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(lean_object* v_origAllocId_1084_, lean_object* v_mask_1085_, lean_object* v_resetJpId_1086_, lean_object* v_isSharedId_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_code_1101_; lean_object* v___x_1102_; 
lean_inc(v_origAllocId_1084_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_origAllocId_1084_);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_isSharedId_1087_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v___x_1096_ = lean_array_get_size(v_mask_1085_);
v___x_1097_ = lean_unsigned_to_nat(2u);
v___x_1098_ = lean_mk_empty_array_with_capacity(v___x_1097_);
v___x_1099_ = lean_array_push(v___x_1098_, v___x_1093_);
v___x_1100_ = lean_array_push(v___x_1099_, v___x_1094_);
v_code_1101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1101_, 0, v_resetJpId_1086_);
lean_ctor_set(v_code_1101_, 1, v___x_1100_);
v___x_1102_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v___x_1096_, v_mask_1085_, v_origAllocId_1084_, v___x_1095_, v_code_1101_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath___boxed(lean_object* v_origAllocId_1103_, lean_object* v_mask_1104_, lean_object* v_resetJpId_1105_, lean_object* v_isSharedId_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_1103_, v_mask_1104_, v_resetJpId_1105_, v_isSharedId_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_mask_1104_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(lean_object* v_upperBound_1113_, lean_object* v_mask_1114_, lean_object* v_origAllocId_1115_, lean_object* v_inst_1116_, lean_object* v_R_1117_, lean_object* v_a_1118_, lean_object* v_b_1119_, lean_object* v_c_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg(v_upperBound_1113_, v_mask_1114_, v_origAllocId_1115_, v_a_1118_, v_b_1119_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___boxed(lean_object* v_upperBound_1127_, lean_object* v_mask_1128_, lean_object* v_origAllocId_1129_, lean_object* v_inst_1130_, lean_object* v_R_1131_, lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v_c_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0(v_upperBound_1127_, v_mask_1128_, v_origAllocId_1129_, v_inst_1130_, v_R_1131_, v_a_1132_, v_b_1133_, v_c_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v_mask_1128_);
lean_dec(v_upperBound_1127_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(lean_object* v_as_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_b_1144_){
_start:
{
lean_object* v_a_1147_; uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_b_1144_);
return v___x_1152_;
}
else
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_array_uget_borrowed(v_as_1141_, v_i_1143_);
if (lean_obj_tag(v_a_1153_) == 1)
{
lean_object* v_val_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
v_val_1154_ = lean_ctor_get(v_a_1153_, 0);
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = 0;
lean_inc(v_val_1154_);
v___x_1157_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v___x_1157_, 0, v_val_1154_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
lean_ctor_set(v___x_1157_, 2, v_b_1144_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3, v___x_1151_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 1, v___x_1156_);
v_a_1147_ = v___x_1157_;
goto v___jp_1146_;
}
else
{
v_a_1147_ = v_b_1144_;
goto v___jp_1146_;
}
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1143_, v___x_1148_);
v_i_1143_ = v___x_1149_;
v_b_1144_ = v_a_1147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg___boxed(lean_object* v_as_1158_, lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_b_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_as_1158_, v_sz_boxed_1163_, v_i_boxed_1164_, v_b_1161_);
lean_dec_ref(v_as_1158_);
return v_res_1165_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_unsigned_to_nat(2u);
v___x_1168_ = lean_mk_empty_array_with_capacity(v___x_1167_);
v___x_1169_ = lean_array_push(v___x_1168_, v___x_1166_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(lean_object* v_origAllocId_1170_, lean_object* v_mask_1171_, lean_object* v_resetJpId_1172_, lean_object* v_isSharedId_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_code_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; lean_object* v_code_1186_; size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_isSharedId_1173_);
v___x_1180_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath___closed__0);
v___x_1181_ = lean_array_push(v___x_1180_, v___x_1179_);
v_code_1182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_code_1182_, 0, v_resetJpId_1172_);
lean_ctor_set(v_code_1182_, 1, v___x_1181_);
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = 1;
v___x_1185_ = 0;
v_code_1186_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_code_1186_, 0, v_origAllocId_1170_);
lean_ctor_set(v_code_1186_, 1, v___x_1183_);
lean_ctor_set(v_code_1186_, 2, v_code_1182_);
lean_ctor_set_uint8(v_code_1186_, sizeof(void*)*3, v___x_1184_);
lean_ctor_set_uint8(v_code_1186_, sizeof(void*)*3 + 1, v___x_1185_);
v_sz_1187_ = lean_array_size(v_mask_1171_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath_spec__0___redArg(v_mask_1171_, v_sz_1187_, v___x_1188_, v_code_1186_);
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
uint8_t v___x_1230_; 
v___x_1230_ = lean_nat_dec_lt(v_a_1226_, v_upperBound_1222_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_a_1226_);
lean_dec(v_resetTokenId_1225_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_b_1227_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_array_fget_borrowed(v_args_1223_, v_a_1226_);
v___x_1233_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_isSelfOset___redArg(v_origAllocId_1224_, v_a_1226_, v___x_1232_, v___y_1228_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_a_1236_; uint8_t v___x_1240_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
v___x_1240_ = lean_unbox(v_a_1234_);
lean_dec(v_a_1234_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v___x_1232_);
lean_inc(v_a_1226_);
lean_inc(v_resetTokenId_1225_);
v___x_1241_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v___x_1241_, 0, v_resetTokenId_1225_);
lean_ctor_set(v___x_1241_, 1, v_a_1226_);
lean_ctor_set(v___x_1241_, 2, v___x_1232_);
lean_ctor_set(v___x_1241_, 3, v_b_1227_);
v_a_1236_ = v___x_1241_;
goto v___jp_1235_;
}
else
{
v_a_1236_ = v_b_1227_;
goto v___jp_1235_;
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_a_1226_, v___x_1237_);
lean_dec(v_a_1226_);
v_a_1226_ = v___x_1238_;
v_b_1227_ = v_a_1236_;
goto _start;
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_b_1227_);
lean_dec(v_a_1226_);
lean_dec(v_resetTokenId_1225_);
v_a_1242_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1233_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1233_);
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
lean_dec_ref(v___x_1345_);
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
lean_object* v_a_1351_; lean_object* v_fvarId_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1368_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
v_fvarId_1352_ = lean_ctor_get(v_a_1351_, 0);
lean_inc_n(v_fvarId_1352_, 2);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_fvarId_1352_);
v___x_1354_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_remapSets___redArg(v_fvarId_1352_, v_selfSets_1338_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1368_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1368_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_mk_empty_array_with_capacity(v___x_1359_);
v___x_1361_ = lean_array_push(v___x_1360_, v___x_1353_);
v___x_1362_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_contJpId_1337_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1348_, v_a_1355_, v___x_1362_);
lean_dec(v_a_1355_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1351_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1364_);
v___x_1366_ = v___x_1357_;
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
uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = 1;
v___x_1454_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_toApplicative_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1496_; 
v___x_1461_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__0);
v___x_1462_ = l_StateRefT_x27_instMonad___redArg(v___x_1461_);
v_toApplicative_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___x_1462_, 1);
lean_dec(v_unused_1497_);
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1496_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_toApplicative_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1496_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_toFunctor_1467_; lean_object* v_toSeq_1468_; lean_object* v_toSeqLeft_1469_; lean_object* v_toSeqRight_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1494_; 
v_toFunctor_1467_ = lean_ctor_get(v_toApplicative_1463_, 0);
v_toSeq_1468_ = lean_ctor_get(v_toApplicative_1463_, 2);
v_toSeqLeft_1469_ = lean_ctor_get(v_toApplicative_1463_, 3);
v_toSeqRight_1470_ = lean_ctor_get(v_toApplicative_1463_, 4);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_toApplicative_1463_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_toApplicative_1463_, 1);
lean_dec(v_unused_1495_);
v___x_1472_ = v_toApplicative_1463_;
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_toSeqRight_1470_);
lean_inc(v_toSeqLeft_1469_);
lean_inc(v_toSeq_1468_);
lean_inc(v_toFunctor_1467_);
lean_dec(v_toApplicative_1463_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1494_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___f_1476_; lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___x_1483_; 
v___f_1474_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__1));
v___f_1475_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1467_);
v___f_1476_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1476_, 0, v_toFunctor_1467_);
v___f_1477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1477_, 0, v_toFunctor_1467_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___f_1476_);
lean_ctor_set(v___x_1478_, 1, v___f_1477_);
v___f_1479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1479_, 0, v_toSeqRight_1470_);
v___f_1480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1480_, 0, v_toSeqLeft_1469_);
v___f_1481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1481_, 0, v_toSeq_1468_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 4, v___f_1479_);
lean_ctor_set(v___x_1472_, 3, v___f_1480_);
lean_ctor_set(v___x_1472_, 2, v___f_1481_);
lean_ctor_set(v___x_1472_, 1, v___f_1474_);
lean_ctor_set(v___x_1472_, 0, v___x_1478_);
v___x_1483_ = v___x_1472_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___f_1474_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v___f_1481_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v___f_1480_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v___f_1479_);
v___x_1483_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___f_1475_);
lean_ctor_set(v___x_1465_, 0, v___x_1483_);
v___x_1485_ = v___x_1465_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___f_1475_);
v___x_1485_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___f_1489_; lean_object* v___x_7080__overap_1490_; lean_object* v___x_1491_; 
v___x_1486_ = l_StateRefT_x27_instMonad___redArg(v___x_1485_);
v___x_1487_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___closed__0);
v___x_1488_ = l_instInhabitedOfMonad___redArg(v___x_1486_, v___x_1487_);
v___f_1489_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1489_, 0, v___x_1488_);
v___x_7080__overap_1490_ = lean_panic_fn_borrowed(v___f_1489_, v_msg_1455_);
lean_dec_ref(v___f_1489_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
v___x_1491_ = lean_apply_5(v___x_7080__overap_1490_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, lean_box(0));
return v___x_1491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2___boxed(lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v_msg_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1504_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_box(0);
v___x_1512_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__3));
v___x_1513_ = l_Lean_Expr_const___override(v___x_1512_, v___x_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed(lean_object* v_resetTokenId_1514_, lean_object* v_origAllocId_1515_, lean_object* v_isSharedId_1516_, lean_object* v_resultType_1517_, lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(v_resetTokenId_1514_, v_origAllocId_1515_, v_isSharedId_1516_, v_resultType_1517_, v_x_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(lean_object* v_resetTokenId_1525_, lean_object* v_origAllocId_1526_, lean_object* v_isSharedId_1527_, lean_object* v_resultType_1528_, lean_object* v_i_1529_, lean_object* v_as_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = lean_array_get_size(v_as_1530_);
v___x_1537_ = lean_nat_dec_lt(v_i_1529_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec(v_i_1529_);
lean_dec_ref(v_resultType_1528_);
lean_dec(v_isSharedId_1527_);
lean_dec(v_origAllocId_1526_);
lean_dec(v_resetTokenId_1525_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_as_1530_);
return v___x_1538_;
}
else
{
lean_object* v___f_1539_; lean_object* v_a_1540_; lean_object* v___x_1541_; 
lean_inc_ref(v_resultType_1528_);
lean_inc(v_isSharedId_1527_);
lean_inc(v_origAllocId_1526_);
lean_inc(v_resetTokenId_1525_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1539_, 0, v_resetTokenId_1525_);
lean_closure_set(v___f_1539_, 1, v_origAllocId_1526_);
lean_closure_set(v___f_1539_, 2, v_isSharedId_1527_);
lean_closure_set(v___f_1539_, 3, v_resultType_1528_);
v_a_1540_ = lean_array_fget_borrowed(v_as_1530_, v_i_1529_);
lean_inc(v_a_1540_);
v___x_1541_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_1540_, v___f_1539_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; size_t v___x_1543_; size_t v___x_1544_; uint8_t v___x_1545_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___x_1543_ = lean_ptr_addr(v_a_1540_);
v___x_1544_ = lean_ptr_addr(v_a_1542_);
v___x_1545_ = lean_usize_dec_eq(v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v_i_1529_, v___x_1546_);
v___x_1548_ = lean_array_fset(v_as_1530_, v_i_1529_, v_a_1542_);
lean_dec(v_i_1529_);
v_i_1529_ = v___x_1547_;
v_as_1530_ = v___x_1548_;
goto _start;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v_a_1542_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_add(v_i_1529_, v___x_1550_);
lean_dec(v_i_1529_);
v_i_1529_ = v___x_1551_;
goto _start;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_as_1530_);
lean_dec(v_i_1529_);
lean_dec_ref(v_resultType_1528_);
lean_dec(v_isSharedId_1527_);
lean_dec(v_origAllocId_1526_);
lean_dec(v_resetTokenId_1525_);
v_a_1553_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1541_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1541_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1563_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__6));
v___x_1564_ = lean_unsigned_to_nat(6u);
v___x_1565_ = lean_unsigned_to_nat(208u);
v___x_1566_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__5));
v___x_1567_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor_spec__1___redArg___closed__1));
v___x_1568_ = l_mkPanicMessageWithDecl(v___x_1567_, v___x_1566_, v___x_1565_, v___x_1564_, v___x_1563_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(lean_object* v_resetTokenId_1569_, lean_object* v_code_1570_, lean_object* v_origAllocId_1571_, lean_object* v_isSharedId_1572_, lean_object* v_currentRetType_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
switch(lean_obj_tag(v_code_1570_))
{
case 0:
{
lean_object* v_decl_1579_; lean_object* v_value_1580_; 
v_decl_1579_ = lean_ctor_get(v_code_1570_, 0);
v_value_1580_ = lean_ctor_get(v_decl_1579_, 3);
lean_inc(v_value_1580_);
if (lean_obj_tag(v_value_1580_) == 12)
{
lean_object* v_k_1581_; lean_object* v_fvarId_1582_; lean_object* v_binderName_1583_; lean_object* v_type_1584_; lean_object* v_var_1585_; lean_object* v_i_1586_; uint8_t v_updateHeader_1587_; lean_object* v_args_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1704_; 
v_k_1581_ = lean_ctor_get(v_code_1570_, 1);
v_fvarId_1582_ = lean_ctor_get(v_decl_1579_, 0);
v_binderName_1583_ = lean_ctor_get(v_decl_1579_, 1);
v_type_1584_ = lean_ctor_get(v_decl_1579_, 2);
v_var_1585_ = lean_ctor_get(v_value_1580_, 0);
v_i_1586_ = lean_ctor_get(v_value_1580_, 1);
v_updateHeader_1587_ = lean_ctor_get_uint8(v_value_1580_, sizeof(void*)*3);
v_args_1588_ = lean_ctor_get(v_value_1580_, 2);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_value_1580_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1590_ = v_value_1580_;
v_isShared_1591_ = v_isSharedCheck_1704_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_args_1588_);
lean_inc(v_i_1586_);
lean_inc(v_var_1585_);
lean_dec(v_value_1580_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1704_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
uint8_t v___x_1592_; 
v___x_1592_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1569_, v_var_1585_);
lean_dec(v_var_1585_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
lean_del_object(v___x_1590_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
lean_inc_ref(v_k_1581_);
v___x_1593_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1581_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1616_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1616_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1616_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
size_t v___x_1598_; size_t v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_ptr_addr(v_k_1581_);
v___x_1599_ = lean_ptr_addr(v_a_1594_);
v___x_1600_ = lean_usize_dec_eq(v___x_1598_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1610_; 
lean_inc_ref(v_decl_1579_);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1611_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1612_);
v___x_1602_ = v_code_1570_;
v_isShared_1603_ = v_isSharedCheck_1610_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v_code_1570_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1610_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v_a_1594_);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_decl_1579_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_a_1594_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1605_);
v___x_1607_ = v___x_1596_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v___x_1614_; 
lean_dec(v_a_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_code_1570_);
v___x_1614_ = v___x_1596_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_code_1570_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_1593_;
}
}
else
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1701_; 
lean_inc_ref(v_k_1581_);
lean_inc_ref(v_decl_1579_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1702_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1703_);
v___x_1618_ = v_code_1570_;
v_isShared_1619_ = v_isSharedCheck_1701_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_code_1570_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1701_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_collectSucceedingSets(v_fvarId_1582_, v_k_1581_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1624_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
v_fst_1622_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_fst_1622_);
v_snd_1623_ = lean_ctor_get(v_a_1621_, 1);
lean_inc(v_snd_1623_);
lean_dec(v_a_1621_);
v___x_1624_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_partitionSelfSets(v_origAllocId_1571_, v_fst_1622_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_fst_1622_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v_fst_1626_; lean_object* v_snd_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref(v___x_1624_);
v_fst_1626_ = lean_ctor_get(v_a_1625_, 0);
lean_inc(v_fst_1626_);
v_snd_1627_ = lean_ctor_get(v_a_1625_, 1);
lean_inc(v_snd_1627_);
lean_dec(v_a_1625_);
v___x_1628_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__1));
v___x_1629_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1628_, v_a_1575_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1635_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref(v___x_1629_);
v___x_1631_ = 1;
v___x_1632_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1631_, v_snd_1627_, v_snd_1623_);
lean_dec(v_snd_1627_);
v___x_1633_ = 0;
lean_inc_ref(v_type_1584_);
lean_inc(v_binderName_1583_);
lean_inc(v_fvarId_1582_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 0);
lean_ctor_set(v___x_1590_, 2, v_type_1584_);
lean_ctor_set(v___x_1590_, 1, v_binderName_1583_);
lean_ctor_set(v___x_1590_, 0, v_fvarId_1582_);
v___x_1635_ = v___x_1590_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_fvarId_1582_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_binderName_1583_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_type_1584_);
v___x_1635_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*3, v___x_1633_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_mk_empty_array_with_capacity(v___x_1636_);
v___x_1638_ = lean_array_push(v___x_1637_, v___x_1635_);
lean_inc_ref(v_currentRetType_1573_);
v___x_1639_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_1631_, v_a_1630_, v_currentRetType_1573_, v___x_1638_, v___x_1632_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_fvarId_1641_; lean_object* v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v_fvarId_1641_ = lean_ctor_get(v_a_1640_, 0);
lean_inc(v_fvarId_1641_);
lean_inc_ref(v_args_1588_);
lean_inc_ref(v_i_1586_);
lean_inc_ref(v_decl_1579_);
v___x_1642_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkSlowPath(v_decl_1579_, v_i_1586_, v_args_1588_, v_fvarId_1641_, v_fst_1626_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
lean_inc(v_fvarId_1641_);
v___x_1644_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_mkFastPath(v_resetTokenId_1569_, v_i_1586_, v_updateHeader_1587_, v_args_1588_, v_fvarId_1641_, v_origAllocId_1571_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_origAllocId_1571_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1644_);
v___x_1646_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_1631_, v_decl_1579_, v_a_1575_);
lean_dec_ref(v_decl_1579_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v___x_1646_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_1648_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_isSharedId_1572_, v___x_1647_, v_currentRetType_1573_, v_a_1643_, v_a_1645_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1659_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1659_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1659_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 2);
lean_ctor_set(v___x_1618_, 1, v_a_1649_);
lean_ctor_set(v___x_1618_, 0, v_a_1640_);
v___x_1654_ = v___x_1618_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1640_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1654_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_dec(v_a_1640_);
lean_del_object(v___x_1618_);
return v___x_1648_;
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1645_);
lean_dec(v_a_1643_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1618_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
v_a_1660_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1646_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1646_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_dec(v_a_1643_);
lean_dec(v_a_1640_);
lean_del_object(v___x_1618_);
lean_dec_ref(v_decl_1579_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
return v___x_1644_;
}
}
else
{
lean_dec(v_a_1640_);
lean_del_object(v___x_1618_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
lean_dec_ref(v_decl_1579_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
return v___x_1642_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_fst_1626_);
lean_del_object(v___x_1618_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
lean_dec_ref(v_decl_1579_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
v_a_1668_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1639_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1639_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_snd_1627_);
lean_dec(v_fst_1626_);
lean_dec(v_snd_1623_);
lean_del_object(v___x_1618_);
lean_del_object(v___x_1590_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
lean_dec_ref(v_decl_1579_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
v_a_1677_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1629_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1629_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_snd_1623_);
lean_del_object(v___x_1618_);
lean_del_object(v___x_1590_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
lean_dec_ref(v_decl_1579_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
v_a_1685_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1624_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1624_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1618_);
lean_del_object(v___x_1590_);
lean_dec_ref(v_args_1588_);
lean_dec_ref(v_i_1586_);
lean_dec_ref(v_decl_1579_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
v_a_1693_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1620_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1620_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
else
{
lean_object* v_k_1705_; lean_object* v___x_1706_; 
lean_dec(v_value_1580_);
v_k_1705_ = lean_ctor_get(v_code_1570_, 1);
lean_inc_ref(v_k_1705_);
v___x_1706_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1705_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1729_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1729_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1729_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
size_t v___x_1711_; size_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1711_ = lean_ptr_addr(v_k_1705_);
v___x_1712_ = lean_ptr_addr(v_a_1707_);
v___x_1713_ = lean_usize_dec_eq(v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
lean_inc_ref(v_decl_1579_);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; lean_object* v_unused_1725_; 
v_unused_1724_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1724_);
v_unused_1725_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1725_);
v___x_1715_ = v_code_1570_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_dec(v_code_1570_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_a_1707_);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_decl_1579_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_a_1707_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1718_);
v___x_1720_ = v___x_1709_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v___x_1727_; 
lean_dec(v_a_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_code_1570_);
v___x_1727_ = v___x_1709_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_code_1570_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_1706_;
}
}
}
case 2:
{
lean_object* v_decl_1730_; lean_object* v_k_1731_; lean_object* v_params_1732_; lean_object* v_type_1733_; lean_object* v_value_1734_; lean_object* v___x_1735_; 
v_decl_1730_ = lean_ctor_get(v_code_1570_, 0);
v_k_1731_ = lean_ctor_get(v_code_1570_, 1);
v_params_1732_ = lean_ctor_get(v_decl_1730_, 2);
v_type_1733_ = lean_ctor_get(v_decl_1730_, 3);
v_value_1734_ = lean_ctor_get(v_decl_1730_, 4);
lean_inc_ref(v_type_1733_);
lean_inc(v_isSharedId_1572_);
lean_inc(v_origAllocId_1571_);
lean_inc_ref(v_value_1734_);
lean_inc(v_resetTokenId_1569_);
v___x_1735_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_value_1734_, v_origAllocId_1571_, v_isSharedId_1572_, v_type_1733_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = 1;
lean_inc_ref(v_params_1732_);
lean_inc_ref(v_type_1733_);
lean_inc_ref(v_decl_1730_);
v___x_1738_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1737_, v_decl_1730_, v_type_1733_, v_params_1732_, v_a_1736_, v_a_1575_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
lean_inc_ref(v_k_1731_);
v___x_1740_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1731_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1768_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1768_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1768_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
uint8_t v___y_1746_; size_t v___x_1762_; size_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = lean_ptr_addr(v_k_1731_);
v___x_1763_ = lean_ptr_addr(v_a_1741_);
v___x_1764_ = lean_usize_dec_eq(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
v___y_1746_ = v___x_1764_;
goto v___jp_1745_;
}
else
{
size_t v___x_1765_; size_t v___x_1766_; uint8_t v___x_1767_; 
v___x_1765_ = lean_ptr_addr(v_decl_1730_);
v___x_1766_ = lean_ptr_addr(v_a_1739_);
v___x_1767_ = lean_usize_dec_eq(v___x_1765_, v___x_1766_);
v___y_1746_ = v___x_1767_;
goto v___jp_1745_;
}
v___jp_1745_:
{
if (v___y_1746_ == 0)
{
lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1756_; 
v_isSharedCheck_1756_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; lean_object* v_unused_1758_; 
v_unused_1757_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1758_);
v___x_1748_ = v_code_1570_;
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
else
{
lean_dec(v_code_1570_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1756_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v_a_1741_);
lean_ctor_set(v___x_1748_, 0, v_a_1739_);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1739_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_a_1741_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1751_);
v___x_1753_ = v___x_1743_;
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
lean_object* v___x_1760_; 
lean_dec(v_a_1741_);
lean_dec(v_a_1739_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_code_1570_);
v___x_1760_ = v___x_1743_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_code_1570_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
else
{
lean_dec(v_a_1739_);
lean_dec_ref(v_code_1570_);
return v___x_1740_;
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_code_1570_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
v_a_1769_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1738_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1738_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
return v___x_1735_;
}
}
case 4:
{
lean_object* v_cases_1777_; lean_object* v_typeName_1778_; lean_object* v_resultType_1779_; lean_object* v_discr_1780_; lean_object* v_alts_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v_currentRetType_1573_);
v_cases_1777_ = lean_ctor_get(v_code_1570_, 0);
lean_inc_ref(v_cases_1777_);
v_typeName_1778_ = lean_ctor_get(v_cases_1777_, 0);
v_resultType_1779_ = lean_ctor_get(v_cases_1777_, 1);
v_discr_1780_ = lean_ctor_get(v_cases_1777_, 2);
v_alts_1781_ = lean_ctor_get(v_cases_1777_, 3);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_cases_1777_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1783_ = v_cases_1777_;
v_isShared_1784_ = v_isSharedCheck_1820_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_alts_1781_);
lean_inc(v_discr_1780_);
lean_inc(v_resultType_1779_);
lean_inc(v_typeName_1778_);
lean_dec(v_cases_1777_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1820_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1781_);
lean_inc_ref(v_resultType_1779_);
v___x_1786_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_1569_, v_origAllocId_1571_, v_isSharedId_1572_, v_resultType_1779_, v___x_1785_, v_alts_1781_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1811_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
size_t v___x_1791_; size_t v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = lean_ptr_addr(v_alts_1781_);
lean_dec_ref(v_alts_1781_);
v___x_1792_ = lean_ptr_addr(v_a_1787_);
v___x_1793_ = lean_usize_dec_eq(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1806_; 
v_isSharedCheck_1806_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1807_);
v___x_1795_ = v_code_1570_;
v_isShared_1796_ = v_isSharedCheck_1806_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v_code_1570_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1806_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 3, v_a_1787_);
v___x_1798_ = v___x_1783_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_typeName_1778_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_resultType_1779_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_discr_1780_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v_a_1787_);
v___x_1798_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1798_);
v___x_1800_ = v___x_1795_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1800_);
v___x_1802_ = v___x_1789_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
else
{
lean_object* v___x_1809_; 
lean_dec(v_a_1787_);
lean_del_object(v___x_1783_);
lean_dec(v_discr_1780_);
lean_dec_ref(v_resultType_1779_);
lean_dec(v_typeName_1778_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v_code_1570_);
v___x_1809_ = v___x_1789_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_code_1570_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_del_object(v___x_1783_);
lean_dec_ref(v_alts_1781_);
lean_dec(v_discr_1780_);
lean_dec_ref(v_resultType_1779_);
lean_dec(v_typeName_1778_);
lean_dec_ref(v_code_1570_);
v_a_1812_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1786_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1786_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_1821_; lean_object* v_i_1822_; lean_object* v_y_1823_; lean_object* v_k_1824_; lean_object* v___x_1825_; 
v_fvarId_1821_ = lean_ctor_get(v_code_1570_, 0);
v_i_1822_ = lean_ctor_get(v_code_1570_, 1);
v_y_1823_ = lean_ctor_get(v_code_1570_, 2);
v_k_1824_ = lean_ctor_get(v_code_1570_, 3);
lean_inc_ref(v_k_1824_);
v___x_1825_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1824_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1850_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1850_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1850_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
size_t v___x_1830_; size_t v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_ptr_addr(v_k_1824_);
v___x_1831_ = lean_ptr_addr(v_a_1826_);
v___x_1832_ = lean_usize_dec_eq(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1842_; 
lean_inc(v_y_1823_);
lean_inc(v_i_1822_);
lean_inc(v_fvarId_1821_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; lean_object* v_unused_1846_; 
v_unused_1843_ = lean_ctor_get(v_code_1570_, 3);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_code_1570_, 2);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1846_);
v___x_1834_ = v_code_1570_;
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v_code_1570_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 3, v_a_1826_);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_fvarId_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_i_1822_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_y_1823_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_a_1826_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1837_);
v___x_1839_ = v___x_1828_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v___x_1848_; 
lean_dec(v_a_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v_code_1570_);
v___x_1848_ = v___x_1828_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_code_1570_);
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
lean_dec_ref(v_code_1570_);
return v___x_1825_;
}
}
case 8:
{
lean_object* v_fvarId_1851_; lean_object* v_i_1852_; lean_object* v_y_1853_; lean_object* v_k_1854_; lean_object* v___x_1855_; 
v_fvarId_1851_ = lean_ctor_get(v_code_1570_, 0);
v_i_1852_ = lean_ctor_get(v_code_1570_, 1);
v_y_1853_ = lean_ctor_get(v_code_1570_, 2);
v_k_1854_ = lean_ctor_get(v_code_1570_, 3);
lean_inc_ref(v_k_1854_);
v___x_1855_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1854_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1880_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1880_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1880_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
size_t v___x_1860_; size_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_ptr_addr(v_k_1854_);
v___x_1861_ = lean_ptr_addr(v_a_1856_);
v___x_1862_ = lean_usize_dec_eq(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
lean_inc(v_y_1853_);
lean_inc(v_i_1852_);
lean_inc(v_fvarId_1851_);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; lean_object* v_unused_1874_; lean_object* v_unused_1875_; lean_object* v_unused_1876_; 
v_unused_1873_ = lean_ctor_get(v_code_1570_, 3);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_code_1570_, 2);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1876_);
v___x_1864_ = v_code_1570_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v_code_1570_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 3, v_a_1856_);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fvarId_1851_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_i_1852_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_y_1853_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_a_1856_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1867_);
v___x_1869_ = v___x_1858_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v___x_1878_; 
lean_dec(v_a_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_code_1570_);
v___x_1878_ = v___x_1858_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_code_1570_);
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
lean_dec_ref(v_code_1570_);
return v___x_1855_;
}
}
case 9:
{
lean_object* v_fvarId_1881_; lean_object* v_i_1882_; lean_object* v_offset_1883_; lean_object* v_y_1884_; lean_object* v_ty_1885_; lean_object* v_k_1886_; lean_object* v___x_1887_; 
v_fvarId_1881_ = lean_ctor_get(v_code_1570_, 0);
v_i_1882_ = lean_ctor_get(v_code_1570_, 1);
v_offset_1883_ = lean_ctor_get(v_code_1570_, 2);
v_y_1884_ = lean_ctor_get(v_code_1570_, 3);
v_ty_1885_ = lean_ctor_get(v_code_1570_, 4);
v_k_1886_ = lean_ctor_get(v_code_1570_, 5);
lean_inc_ref(v_k_1886_);
v___x_1887_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1886_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1914_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1914_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1914_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
size_t v___x_1892_; size_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = lean_ptr_addr(v_k_1886_);
v___x_1893_ = lean_ptr_addr(v_a_1888_);
v___x_1894_ = lean_usize_dec_eq(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1904_; 
lean_inc_ref(v_ty_1885_);
lean_inc(v_y_1884_);
lean_inc(v_offset_1883_);
lean_inc(v_i_1882_);
lean_inc(v_fvarId_1881_);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; lean_object* v_unused_1908_; lean_object* v_unused_1909_; lean_object* v_unused_1910_; 
v_unused_1905_ = lean_ctor_get(v_code_1570_, 5);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_code_1570_, 4);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_code_1570_, 3);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v_code_1570_, 2);
lean_dec(v_unused_1908_);
v_unused_1909_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1910_);
v___x_1896_ = v_code_1570_;
v_isShared_1897_ = v_isSharedCheck_1904_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_code_1570_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1904_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 5, v_a_1888_);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_fvarId_1881_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_i_1882_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_offset_1883_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_y_1884_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_ty_1885_);
lean_ctor_set(v_reuseFailAlloc_1903_, 5, v_a_1888_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1899_);
v___x_1901_ = v___x_1890_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v_a_1888_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v_code_1570_);
v___x_1912_ = v___x_1890_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_code_1570_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_1887_;
}
}
case 10:
{
lean_object* v_fvarId_1915_; lean_object* v_cidx_1916_; lean_object* v_k_1917_; lean_object* v___x_1918_; 
v_fvarId_1915_ = lean_ctor_get(v_code_1570_, 0);
v_cidx_1916_ = lean_ctor_get(v_code_1570_, 1);
v_k_1917_ = lean_ctor_get(v_code_1570_, 2);
lean_inc_ref(v_k_1917_);
v___x_1918_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1917_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1942_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1942_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1942_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
size_t v___x_1923_; size_t v___x_1924_; uint8_t v___x_1925_; 
v___x_1923_ = lean_ptr_addr(v_k_1917_);
v___x_1924_ = lean_ptr_addr(v_a_1919_);
v___x_1925_ = lean_usize_dec_eq(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1935_; 
lean_inc(v_cidx_1916_);
lean_inc(v_fvarId_1915_);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; lean_object* v_unused_1938_; 
v_unused_1936_ = lean_ctor_get(v_code_1570_, 2);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1938_);
v___x_1927_ = v_code_1570_;
v_isShared_1928_ = v_isSharedCheck_1935_;
goto v_resetjp_1926_;
}
else
{
lean_dec(v_code_1570_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1935_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 2, v_a_1919_);
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_fvarId_1915_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_cidx_1916_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_a_1919_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1930_);
v___x_1932_ = v___x_1921_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v___x_1940_; 
lean_dec(v_a_1919_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_code_1570_);
v___x_1940_ = v___x_1921_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_code_1570_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_1918_;
}
}
case 11:
{
lean_object* v_fvarId_1943_; lean_object* v_n_1944_; uint8_t v_check_1945_; uint8_t v_persistent_1946_; lean_object* v_k_1947_; lean_object* v___x_1948_; 
v_fvarId_1943_ = lean_ctor_get(v_code_1570_, 0);
v_n_1944_ = lean_ctor_get(v_code_1570_, 1);
v_check_1945_ = lean_ctor_get_uint8(v_code_1570_, sizeof(void*)*3);
v_persistent_1946_ = lean_ctor_get_uint8(v_code_1570_, sizeof(void*)*3 + 1);
v_k_1947_ = lean_ctor_get(v_code_1570_, 2);
lean_inc_ref(v_k_1947_);
v___x_1948_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1947_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1972_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1972_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1972_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
size_t v___x_1953_; size_t v___x_1954_; uint8_t v___x_1955_; 
v___x_1953_ = lean_ptr_addr(v_k_1947_);
v___x_1954_ = lean_ptr_addr(v_a_1949_);
v___x_1955_ = lean_usize_dec_eq(v___x_1953_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
lean_inc(v_n_1944_);
lean_inc(v_fvarId_1943_);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; lean_object* v_unused_1967_; lean_object* v_unused_1968_; 
v_unused_1966_ = lean_ctor_get(v_code_1570_, 2);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1968_);
v___x_1957_ = v_code_1570_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v_code_1570_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 2, v_a_1949_);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_fvarId_1943_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_n_1944_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_a_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3, v_check_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3 + 1, v_persistent_1946_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1960_);
v___x_1962_ = v___x_1951_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v___x_1970_; 
lean_dec(v_a_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_code_1570_);
v___x_1970_ = v___x_1951_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_code_1570_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_1948_;
}
}
case 12:
{
lean_object* v_fvarId_1973_; lean_object* v_n_1974_; uint8_t v_check_1975_; uint8_t v_persistent_1976_; lean_object* v_k_1977_; uint8_t v___x_1978_; 
v_fvarId_1973_ = lean_ctor_get(v_code_1570_, 0);
v_n_1974_ = lean_ctor_get(v_code_1570_, 1);
v_check_1975_ = lean_ctor_get_uint8(v_code_1570_, sizeof(void*)*3);
v_persistent_1976_ = lean_ctor_get_uint8(v_code_1570_, sizeof(void*)*3 + 1);
v_k_1977_ = lean_ctor_get(v_code_1570_, 2);
v___x_1978_ = l_Lean_instBEqFVarId_beq(v_resetTokenId_1569_, v_fvarId_1973_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_inc_ref(v_k_1977_);
v___x_1979_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_1977_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2003_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2003_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2003_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
size_t v___x_1984_; size_t v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = lean_ptr_addr(v_k_1977_);
v___x_1985_ = lean_ptr_addr(v_a_1980_);
v___x_1986_ = lean_usize_dec_eq(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1996_; 
lean_inc(v_n_1974_);
lean_inc(v_fvarId_1973_);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1997_ = lean_ctor_get(v_code_1570_, 2);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_1999_);
v___x_1988_ = v_code_1570_;
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
else
{
lean_dec(v_code_1570_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 2, v_a_1980_);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_fvarId_1973_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_n_1974_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_a_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*3, v_check_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*3 + 1, v_persistent_1976_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1991_);
v___x_1993_ = v___x_1982_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v___x_2001_; 
lean_dec(v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_code_1570_);
v___x_2001_ = v___x_1982_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_code_1570_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_1979_;
}
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
lean_inc_ref(v_k_1977_);
lean_inc(v_n_1974_);
lean_dec_ref(v_code_1570_);
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = lean_nat_dec_eq(v_n_1974_, v___x_2004_);
lean_dec(v_n_1974_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_dec_ref(v_k_1977_);
lean_dec(v_resetTokenId_1569_);
v___x_2006_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__7);
v___x_2007_ = l_panic___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__2(v___x_2006_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_resetTokenId_1569_);
lean_ctor_set(v___x_2008_, 1, v_k_1977_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
}
case 13:
{
lean_object* v_fvarId_2010_; lean_object* v_k_2011_; lean_object* v___x_2012_; 
v_fvarId_2010_ = lean_ctor_get(v_code_1570_, 0);
v_k_2011_ = lean_ctor_get(v_code_1570_, 1);
lean_inc_ref(v_k_2011_);
v___x_2012_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_1569_, v_k_2011_, v_origAllocId_1571_, v_isSharedId_1572_, v_currentRetType_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2035_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2035_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2035_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
size_t v___x_2017_; size_t v___x_2018_; uint8_t v___x_2019_; 
v___x_2017_ = lean_ptr_addr(v_k_2011_);
v___x_2018_ = lean_ptr_addr(v_a_2013_);
v___x_2019_ = lean_usize_dec_eq(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2029_; 
lean_inc(v_fvarId_2010_);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_code_1570_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; lean_object* v_unused_2031_; 
v_unused_2030_ = lean_ctor_get(v_code_1570_, 1);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_code_1570_, 0);
lean_dec(v_unused_2031_);
v___x_2021_ = v_code_1570_;
v_isShared_2022_ = v_isSharedCheck_2029_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_code_1570_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2029_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 1, v_a_2013_);
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_fvarId_2010_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_a_2013_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2024_);
v___x_2026_ = v___x_2015_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v___x_2033_; 
lean_dec(v_a_2013_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v_code_1570_);
v___x_2033_ = v___x_2015_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_code_1570_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_dec_ref(v_code_1570_);
return v___x_2012_;
}
}
default: 
{
lean_object* v___x_2036_; 
lean_dec_ref(v_currentRetType_1573_);
lean_dec(v_isSharedId_1572_);
lean_dec(v_origAllocId_1571_);
lean_dec(v_resetTokenId_1569_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_code_1570_);
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___lam__0(lean_object* v_resetTokenId_2037_, lean_object* v_origAllocId_2038_, lean_object* v_isSharedId_2039_, lean_object* v_resultType_2040_, lean_object* v_x_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2037_, v_x_2041_, v_origAllocId_2038_, v_isSharedId_2039_, v_resultType_2040_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1___boxed(lean_object* v_resetTokenId_2048_, lean_object* v_origAllocId_2049_, lean_object* v_isSharedId_2050_, lean_object* v_resultType_2051_, lean_object* v_i_2052_, lean_object* v_as_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__1(v_resetTokenId_2048_, v_origAllocId_2049_, v_isSharedId_2050_, v_resultType_2051_, v_i_2052_, v_as_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___boxed(lean_object* v_resetTokenId_2060_, lean_object* v_code_2061_, lean_object* v_origAllocId_2062_, lean_object* v_isSharedId_2063_, lean_object* v_currentRetType_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_resetTokenId_2060_, v_code_2061_, v_origAllocId_2062_, v_isSharedId_2063_, v_currentRetType_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(lean_object* v_currentRetType_2080_, lean_object* v_ds_2081_, lean_object* v_decl_2082_, lean_object* v_nFields_2083_, lean_object* v_origAllocId_2084_, lean_object* v_k_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor(v_nFields_2083_, v_origAllocId_2084_, v_ds_2081_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2215_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v_fst_2093_ = lean_ctor_get(v_a_2092_, 0);
v_snd_2094_ = lean_ctor_get(v_a_2092_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2096_ = v_a_2092_;
v_isShared_2097_ = v_isSharedCheck_2215_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_inc(v_fst_2093_);
lean_dec(v_a_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2215_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__1));
v___x_2099_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2098_, v_a_2087_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
v___x_2101_ = 1;
v___x_2102_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont___closed__4);
v___x_2103_ = 0;
v___x_2104_ = l_Lean_Compiler_LCNF_mkParam(v___x_2101_, v_a_2100_, v___x_2102_, v___x_2103_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v_fvarId_2106_; lean_object* v_binderName_2107_; lean_object* v_fvarId_2108_; lean_object* v___x_2109_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v_fvarId_2106_ = lean_ctor_get(v_decl_2082_, 0);
v_binderName_2107_ = lean_ctor_get(v_decl_2082_, 1);
v_fvarId_2108_ = lean_ctor_get(v_a_2105_, 0);
lean_inc_ref(v_currentRetType_2080_);
lean_inc(v_fvarId_2108_);
lean_inc(v_origAllocId_2084_);
lean_inc(v_fvarId_2106_);
v___x_2109_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont(v_fvarId_2106_, v_k_2085_, v_origAllocId_2084_, v_fvarId_2108_, v_currentRetType_2080_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_currentRetType_2080_);
v___x_2112_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_a_2110_, v___x_2111_, v_currentRetType_2080_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2198_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2198_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2198_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__3));
v___x_2118_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2117_, v_a_2087_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath_spec__0___redArg___closed__4);
lean_inc(v_binderName_2107_);
lean_inc(v_fvarId_2106_);
v___x_2121_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2121_, 0, v_fvarId_2106_);
lean_ctor_set(v___x_2121_, 1, v_binderName_2107_);
lean_ctor_set(v___x_2121_, 2, v___x_2120_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*3, v___x_2103_);
v___x_2122_ = lean_unsigned_to_nat(2u);
v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2122_);
v___x_2124_ = lean_array_push(v___x_2123_, v___x_2121_);
v___x_2125_ = lean_array_push(v___x_2124_, v_a_2105_);
lean_inc_ref(v_currentRetType_2080_);
v___x_2126_ = l_Lean_Compiler_LCNF_mkFunDecl(v___x_2101_, v_a_2119_, v_currentRetType_2080_, v___x_2125_, v_a_2113_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___closed__5));
v___x_2129_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2128_, v_a_2087_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
lean_inc(v_origAllocId_2084_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 15);
lean_ctor_set(v___x_2115_, 0, v_origAllocId_2084_);
v___x_2132_ = v___x_2115_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(15, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_origAllocId_2084_);
v___x_2132_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2101_, v_a_2130_, v___x_2102_, v___x_2132_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_fvarId_2135_; lean_object* v_fvarId_2136_; lean_object* v___x_2137_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
v_fvarId_2135_ = lean_ctor_get(v_a_2127_, 0);
v_fvarId_2136_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_fvarId_2136_);
lean_inc(v_fvarId_2135_);
lean_inc(v_origAllocId_2084_);
v___x_2137_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkSlowPath(v_origAllocId_2084_, v_snd_2094_, v_fvarId_2135_, v_fvarId_2136_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
lean_inc(v_fvarId_2136_);
lean_inc(v_fvarId_2135_);
v___x_2139_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_mkFastPath(v_origAllocId_2084_, v_snd_2094_, v_fvarId_2135_, v_fvarId_2136_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_snd_2094_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
lean_inc(v_fvarId_2136_);
v___x_2141_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_mkIf___redArg(v_fvarId_2136_, v___x_2102_, v_currentRetType_2080_, v_a_2138_, v_a_2140_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_2101_, v_decl_2082_, v_a_2087_);
lean_dec_ref(v_decl_2082_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2155_; 
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2143_, 0);
lean_dec(v_unused_2156_);
v___x_2145_ = v___x_2143_;
v_isShared_2146_ = v_isSharedCheck_2155_;
goto v_resetjp_2144_;
}
else
{
lean_dec(v___x_2143_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2155_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v_a_2142_);
lean_ctor_set(v___x_2096_, 0, v_a_2134_);
v___x_2148_ = v___x_2096_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2134_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_a_2142_);
v___x_2148_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_a_2127_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2101_, v_fst_2093_, v___x_2149_);
lean_dec(v_fst_2093_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2150_);
v___x_2152_ = v___x_2145_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2134_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2096_);
lean_dec(v_fst_2093_);
v_a_2157_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2143_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2143_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_dec(v_a_2134_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2096_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_decl_2082_);
return v___x_2141_;
}
}
else
{
lean_dec(v_a_2138_);
lean_dec(v_a_2134_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2096_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
return v___x_2139_;
}
}
else
{
lean_dec(v_a_2134_);
lean_dec(v_a_2127_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
return v___x_2137_;
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v_a_2127_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2165_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2133_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2133_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2127_);
lean_del_object(v___x_2115_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2174_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2129_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2129_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2115_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2182_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2126_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2126_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_2115_);
lean_dec(v_a_2113_);
lean_dec(v_a_2105_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2190_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2118_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2118_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_dec(v_a_2105_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
return v___x_2112_;
}
}
else
{
lean_dec(v_a_2105_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
return v___x_2109_;
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_k_2085_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2199_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2104_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2104_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_k_2085_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2207_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2099_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2099_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v_k_2085_);
lean_dec(v_origAllocId_2084_);
lean_dec_ref(v_decl_2082_);
lean_dec_ref(v_currentRetType_2080_);
v_a_2216_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2091_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2091_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed(lean_object* v_resultType_2224_, lean_object* v_x_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(v_resultType_2224_, v_x_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(lean_object* v_resultType_2232_, lean_object* v_i_2233_, lean_object* v_as_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_array_get_size(v_as_2234_);
v___x_2241_ = lean_nat_dec_lt(v_i_2233_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_i_2233_);
lean_dec_ref(v_resultType_2232_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_as_2234_);
return v___x_2242_;
}
else
{
lean_object* v___f_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; 
lean_inc_ref(v_resultType_2232_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2243_, 0, v_resultType_2232_);
v_a_2244_ = lean_array_fget_borrowed(v_as_2234_, v_i_2233_);
lean_inc(v_a_2244_);
v___x_2245_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_processResetCont_spec__0___redArg(v_a_2244_, v___f_2243_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; size_t v___x_2247_; size_t v___x_2248_; uint8_t v___x_2249_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = lean_ptr_addr(v_a_2244_);
v___x_2248_ = lean_ptr_addr(v_a_2246_);
v___x_2249_ = lean_usize_dec_eq(v___x_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_add(v_i_2233_, v___x_2250_);
v___x_2252_ = lean_array_fset(v_as_2234_, v_i_2233_, v_a_2246_);
lean_dec(v_i_2233_);
v_i_2233_ = v___x_2251_;
v_as_2234_ = v___x_2252_;
goto _start;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec(v_a_2246_);
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_add(v_i_2233_, v___x_2254_);
lean_dec(v_i_2233_);
v_i_2233_ = v___x_2255_;
goto _start;
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_as_2234_);
lean_dec(v_i_2233_);
lean_dec_ref(v_resultType_2232_);
v_a_2257_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2245_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2245_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(lean_object* v_code_2265_, lean_object* v_ds_2266_, lean_object* v_currentRetType_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_code_2274_; lean_object* v_ds_2275_; lean_object* v_k_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; 
switch(lean_obj_tag(v_code_2265_))
{
case 0:
{
lean_object* v_decl_2285_; lean_object* v_value_2286_; 
v_decl_2285_ = lean_ctor_get(v_code_2265_, 0);
v_value_2286_ = lean_ctor_get(v_decl_2285_, 3);
if (lean_obj_tag(v_value_2286_) == 11)
{
lean_object* v_k_2287_; lean_object* v_n_2288_; lean_object* v_var_2289_; lean_object* v___x_2290_; 
lean_inc_ref(v_decl_2285_);
v_k_2287_ = lean_ctor_get(v_code_2265_, 1);
lean_inc_ref(v_k_2287_);
lean_dec_ref(v_code_2265_);
v_n_2288_ = lean_ctor_get(v_value_2286_, 0);
lean_inc(v_n_2288_);
v_var_2289_ = lean_ctor_get(v_value_2286_, 1);
lean_inc(v_var_2289_);
v___x_2290_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2267_, v_ds_2266_, v_decl_2285_, v_n_2288_, v_var_2289_, v_k_2287_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2290_;
}
else
{
lean_object* v_k_2291_; 
v_k_2291_ = lean_ctor_get(v_code_2265_, 1);
lean_inc_ref(v_k_2291_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2291_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
}
case 2:
{
lean_object* v_decl_2292_; lean_object* v_k_2293_; lean_object* v_params_2294_; lean_object* v_type_2295_; lean_object* v_value_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_decl_2292_ = lean_ctor_get(v_code_2265_, 0);
lean_inc_ref(v_decl_2292_);
v_k_2293_ = lean_ctor_get(v_code_2265_, 1);
lean_inc_ref(v_k_2293_);
lean_dec_ref(v_code_2265_);
v_params_2294_ = lean_ctor_get(v_decl_2292_, 2);
lean_inc_ref(v_params_2294_);
v_type_2295_ = lean_ctor_get(v_decl_2292_, 3);
lean_inc_ref_n(v_type_2295_, 2);
v_value_2296_ = lean_ctor_get(v_decl_2292_, 4);
v___x_2297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
lean_inc_ref(v_value_2296_);
v___x_2298_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_value_2296_, v___x_2297_, v_type_2295_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2319_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2319_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2319_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = 1;
v___x_2304_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2303_, v_decl_2292_, v_type_2295_, v_params_2294_, v_a_2299_, v_a_2269_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 2);
lean_ctor_set(v___x_2301_, 0, v_a_2305_);
v___x_2307_ = v___x_2301_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2305_);
v___x_2307_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_array_push(v_ds_2266_, v___x_2307_);
v_code_2265_ = v_k_2293_;
v_ds_2266_ = v___x_2308_;
goto _start;
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_del_object(v___x_2301_);
lean_dec_ref(v_k_2293_);
lean_dec_ref(v_currentRetType_2267_);
lean_dec_ref(v_ds_2266_);
v_a_2311_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2304_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2304_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
else
{
lean_dec_ref(v_type_2295_);
lean_dec_ref(v_params_2294_);
lean_dec_ref(v_k_2293_);
lean_dec_ref(v_decl_2292_);
lean_dec_ref(v_currentRetType_2267_);
lean_dec_ref(v_ds_2266_);
return v___x_2298_;
}
}
case 4:
{
lean_object* v_cases_2320_; lean_object* v_typeName_2321_; lean_object* v_resultType_2322_; lean_object* v_discr_2323_; lean_object* v_alts_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_currentRetType_2267_);
v_cases_2320_ = lean_ctor_get(v_code_2265_, 0);
lean_inc_ref(v_cases_2320_);
v_typeName_2321_ = lean_ctor_get(v_cases_2320_, 0);
v_resultType_2322_ = lean_ctor_get(v_cases_2320_, 1);
v_discr_2323_ = lean_ctor_get(v_cases_2320_, 2);
v_alts_2324_ = lean_ctor_get(v_cases_2320_, 3);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_cases_2320_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2326_ = v_cases_2320_;
v_isShared_2327_ = v_isSharedCheck_2364_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_alts_2324_);
lean_inc(v_discr_2323_);
lean_inc(v_resultType_2322_);
lean_inc(v_typeName_2321_);
lean_dec(v_cases_2320_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2364_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2324_);
lean_inc_ref(v_resultType_2322_);
v___x_2329_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2322_, v___x_2328_, v_alts_2324_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2355_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2355_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2355_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
uint8_t v___x_2334_; lean_object* v___y_2336_; size_t v___x_2341_; size_t v___x_2342_; uint8_t v___x_2343_; 
v___x_2334_ = 1;
v___x_2341_ = lean_ptr_addr(v_alts_2324_);
lean_dec_ref(v_alts_2324_);
v___x_2342_ = lean_ptr_addr(v_a_2330_);
v___x_2343_ = lean_usize_dec_eq(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2353_; 
v_isSharedCheck_2353_ = !lean_is_exclusive(v_code_2265_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v_code_2265_, 0);
lean_dec(v_unused_2354_);
v___x_2345_ = v_code_2265_;
v_isShared_2346_ = v_isSharedCheck_2353_;
goto v_resetjp_2344_;
}
else
{
lean_dec(v_code_2265_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2353_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 3, v_a_2330_);
v___x_2348_ = v___x_2326_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_typeName_2321_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_resultType_2322_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_discr_2323_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_a_2330_);
v___x_2348_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2348_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
v___y_2336_ = v___x_2350_;
goto v___jp_2335_;
}
}
}
}
else
{
lean_dec(v_a_2330_);
lean_del_object(v___x_2326_);
lean_dec(v_discr_2323_);
lean_dec_ref(v_resultType_2322_);
lean_dec(v_typeName_2321_);
v___y_2336_ = v_code_2265_;
goto v___jp_2335_;
}
v___jp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2337_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2334_, v_ds_2266_, v___y_2336_);
lean_dec_ref(v_ds_2266_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2337_);
v___x_2339_ = v___x_2332_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2326_);
lean_dec_ref(v_alts_2324_);
lean_dec(v_discr_2323_);
lean_dec_ref(v_resultType_2322_);
lean_dec(v_typeName_2321_);
lean_dec_ref(v_code_2265_);
lean_dec_ref(v_ds_2266_);
v_a_2356_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2329_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2329_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
case 7:
{
lean_object* v_k_2365_; 
v_k_2365_ = lean_ctor_get(v_code_2265_, 3);
lean_inc_ref(v_k_2365_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2365_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
case 8:
{
lean_object* v_k_2366_; 
v_k_2366_ = lean_ctor_get(v_code_2265_, 3);
lean_inc_ref(v_k_2366_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2366_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
case 9:
{
lean_object* v_k_2367_; 
v_k_2367_ = lean_ctor_get(v_code_2265_, 5);
lean_inc_ref(v_k_2367_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2367_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
case 10:
{
lean_object* v_k_2368_; 
v_k_2368_ = lean_ctor_get(v_code_2265_, 2);
lean_inc_ref(v_k_2368_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2368_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
case 11:
{
lean_object* v_k_2369_; 
v_k_2369_ = lean_ctor_get(v_code_2265_, 2);
lean_inc_ref(v_k_2369_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2369_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
case 12:
{
lean_object* v_k_2370_; 
v_k_2370_ = lean_ctor_get(v_code_2265_, 2);
lean_inc_ref(v_k_2370_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2370_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
case 13:
{
lean_object* v_k_2371_; 
v_k_2371_ = lean_ctor_get(v_code_2265_, 1);
lean_inc_ref(v_k_2371_);
v_code_2274_ = v_code_2265_;
v_ds_2275_ = v_ds_2266_;
v_k_2276_ = v_k_2371_;
v___y_2277_ = v_a_2268_;
v___y_2278_ = v_a_2269_;
v___y_2279_ = v_a_2270_;
v___y_2280_ = v_a_2271_;
goto v___jp_2273_;
}
default: 
{
uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_currentRetType_2267_);
v___x_2372_ = 1;
v___x_2373_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_2372_, v_ds_2266_, v_code_2265_);
lean_dec_ref(v_ds_2266_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
v___jp_2273_:
{
uint8_t v___x_2281_; lean_object* v_d_2282_; lean_object* v___x_2283_; 
v___x_2281_ = 1;
v_d_2282_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_2281_, v_code_2274_);
lean_dec_ref(v_code_2274_);
v___x_2283_ = lean_array_push(v_ds_2275_, v_d_2282_);
v_code_2265_ = v_k_2276_;
v_ds_2266_ = v___x_2283_;
v_a_2268_ = v___y_2277_;
v_a_2269_ = v___y_2278_;
v_a_2270_ = v___y_2279_;
v_a_2271_ = v___y_2280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___lam__0(lean_object* v_resultType_2375_, lean_object* v_x_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2383_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2376_, v___x_2382_, v_resultType_2375_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1___boxed(lean_object* v_resultType_2384_, lean_object* v_i_2385_, lean_object* v_as_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_spec__1(v_resultType_2384_, v_i_2385_, v_as_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse___boxed(lean_object* v_code_2393_, lean_object* v_ds_2394_, lean_object* v_currentRetType_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_code_2393_, v_ds_2394_, v_currentRetType_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand___boxed(lean_object* v_currentRetType_2402_, lean_object* v_ds_2403_, lean_object* v_decl_2404_, lean_object* v_nFields_2405_, lean_object* v_origAllocId_2406_, lean_object* v_k_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse_expand(v_currentRetType_2402_, v_ds_2403_, v_decl_2404_, v_nFields_2405_, v_origAllocId_2406_, v_k_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(lean_object* v_f_2414_, lean_object* v_v_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
if (lean_obj_tag(v_v_2415_) == 0)
{
lean_object* v_code_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2445_; 
v_code_2421_ = lean_ctor_get(v_v_2415_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_v_2415_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2423_ = v_v_2415_;
v_isShared_2424_ = v_isSharedCheck_2445_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_code_2421_);
lean_dec(v_v_2415_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2445_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; 
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
v___x_2425_ = lean_apply_6(v_f_2414_, v_code_2421_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, lean_box(0));
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2436_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2436_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2436_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_a_2426_);
v___x_2431_ = v___x_2423_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_del_object(v___x_2423_);
v_a_2437_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2425_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2425_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
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
}
else
{
lean_object* v___x_2446_; 
lean_dec_ref(v_f_2414_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v_v_2415_);
return v___x_2446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg___boxed(lean_object* v_f_2447_, lean_object* v_v_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2447_, v_v_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(uint8_t v_pu_2455_, lean_object* v_f_2456_, lean_object* v_v_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v_f_2456_, v_v_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___boxed(lean_object* v_pu_2464_, lean_object* v_f_2465_, lean_object* v_v_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v_pu_boxed_2472_; lean_object* v_res_2473_; 
v_pu_boxed_2472_ = lean_unbox(v_pu_2464_);
v_res_2473_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0(v_pu_boxed_2472_, v_f_2465_, v_v_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(lean_object* v_toSignature_2474_, lean_object* v_x_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_type_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_type_2481_ = lean_ctor_get(v_toSignature_2474_, 2);
lean_inc_ref(v_type_2481_);
lean_dec_ref(v_toSignature_2474_);
v___x_2482_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_eraseProjIncFor___closed__0));
v___x_2483_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Code_expandResetReuse(v_x_2475_, v___x_2482_, v_type_2481_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed(lean_object* v_toSignature_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0(v_toSignature_2484_, v_x_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(lean_object* v_decl_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2493_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2536_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2536_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2536_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
uint8_t v_resetReuse_2503_; 
v_resetReuse_2503_ = lean_ctor_get_uint8(v_a_2499_, sizeof(void*)*4 + 2);
lean_dec(v_a_2499_);
if (v_resetReuse_2503_ == 0)
{
lean_object* v___x_2505_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v_decl_2492_);
v___x_2505_ = v___x_2501_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_decl_2492_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
else
{
lean_object* v_toSignature_2507_; lean_object* v_value_2508_; uint8_t v_recursive_2509_; lean_object* v_inlineAttr_x3f_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2535_; 
lean_del_object(v___x_2501_);
v_toSignature_2507_ = lean_ctor_get(v_decl_2492_, 0);
v_value_2508_ = lean_ctor_get(v_decl_2492_, 1);
v_recursive_2509_ = lean_ctor_get_uint8(v_decl_2492_, sizeof(void*)*3);
v_inlineAttr_x3f_2510_ = lean_ctor_get(v_decl_2492_, 2);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_decl_2492_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2512_ = v_decl_2492_;
v_isShared_2513_ = v_isSharedCheck_2535_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_inlineAttr_x3f_2510_);
lean_inc(v_value_2508_);
lean_inc(v_toSignature_2507_);
lean_dec(v_decl_2492_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2535_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___f_2514_; lean_object* v___x_2515_; 
lean_inc_ref(v_toSignature_2507_);
v___f_2514_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2514_, 0, v_toSignature_2507_);
v___x_2515_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse_spec__0___redArg(v___f_2514_, v_value_2508_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2526_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2526_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2526_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v_a_2516_);
v___x_2521_ = v___x_2512_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_toSignature_2507_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_a_2516_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_inlineAttr_x3f_2510_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, sizeof(void*)*3, v_recursive_2509_);
v___x_2521_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2521_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_del_object(v___x_2512_);
lean_dec(v_inlineAttr_x3f_2510_);
lean_dec_ref(v_toSignature_2507_);
v_a_2527_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2515_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2515_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v_decl_2492_);
v_a_2537_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2498_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2498_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse___boxed(lean_object* v_decl_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_Decl_expandResetReuse(v_decl_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
return v_res_2551_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__2));
v___x_2558_ = 2;
v___x_2559_ = ((lean_object*)(l_Lean_Compiler_LCNF_expandResetReuse___closed__1));
v___x_2560_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_2559_, v___x_2558_, v___x_2557_, v___x_2556_);
return v___x_2560_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_expandResetReuse(void){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_obj_once(&l_Lean_Compiler_LCNF_expandResetReuse___closed__3, &l_Lean_Compiler_LCNF_expandResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_expandResetReuse___closed__3);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_unsigned_to_nat(2743268278u);
v___x_2618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2619_ = l_Lean_Name_num___override(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2622_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2623_ = l_Lean_Name_str___override(v___x_2622_, v___x_2621_);
return v___x_2623_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2626_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2627_ = l_Lean_Name_str___override(v___x_2626_, v___x_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_unsigned_to_nat(2u);
v___x_2629_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2630_ = l_Lean_Name_num___override(v___x_2629_, v___x_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2632_; uint8_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2632_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_));
v___x_2633_ = 1;
v___x_2634_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_);
v___x_2635_ = l_Lean_registerTraceClass(v___x_2632_, v___x_2633_, v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2____boxed(lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l___private_Lean_Compiler_LCNF_ExpandResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExpandResetReuse_2743268278____hygCtx___hyg_2_();
return v_res_2637_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
