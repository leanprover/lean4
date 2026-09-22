// Lean compiler output
// Module: Lean.Compiler.LCNF.ResetReuse
// Imports: public import Lean.Compiler.LCNF.CompilerM public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.LiveVars import Lean.Compiler.LCNF.DependsOn import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.PropagateBorrow
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(uint8_t, lean_object*);
lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_isFVarLiveIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_applyOwnedness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t l_Lean_Compiler_LCNF_instBEqOwnedness_beq(uint8_t, uint8_t);
uint8_t l_Lean_Compiler_LCNF_CtorInfo_isScalar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateContImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.S.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Compiler.LCNF.ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.D.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Code.insertResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t, lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "_private.Lean.Compiler.LCNF.ResetReuse.0.Lean.Compiler.LCNF.Decl.insertResetReuseCore.collectResets"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "resetReuse"};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 201, 93, 114, 179, 16, 247, 72)}};
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_insertResetReuse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_insertResetReuse;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_insertResetReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 22, 75, 214, 119, 69, 48, 225)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ResetReuse"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 165, 194, 12, 198, 157, 117, 65)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(105, 150, 117, 254, 63, 70, 178, 234)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 242, 201, 181, 138, 172, 149, 255)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 154, 112, 50, 132, 225, 68, 23)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 182, 243, 139, 183, 248, 56, 98)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 130, 185, 126, 60, 87, 109, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 224, 225, 246, 174, 48, 45, 78)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(146, 47, 104, 191, 68, 113, 248, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 193, 129, 108, 61, 130, 124, 18)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 251, 249, 254, 208, 86, 150, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 85, 80, 162, 8, 82, 178, 101)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(lean_object* v_c_u2081_1_, lean_object* v_c_u2082_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_name_5_; lean_object* v_size_6_; lean_object* v_usize_7_; lean_object* v_ssize_8_; lean_object* v_name_9_; lean_object* v_size_10_; lean_object* v_usize_11_; lean_object* v_ssize_12_; uint8_t v___x_13_; 
v_name_5_ = lean_ctor_get(v_c_u2081_1_, 0);
v_size_6_ = lean_ctor_get(v_c_u2081_1_, 2);
v_usize_7_ = lean_ctor_get(v_c_u2081_1_, 3);
v_ssize_8_ = lean_ctor_get(v_c_u2081_1_, 4);
v_name_9_ = lean_ctor_get(v_c_u2082_2_, 0);
v_size_10_ = lean_ctor_get(v_c_u2082_2_, 2);
v_usize_11_ = lean_ctor_get(v_c_u2082_2_, 3);
v_ssize_12_ = lean_ctor_get(v_c_u2082_2_, 4);
v___x_13_ = lean_nat_dec_eq(v_size_6_, v_size_10_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_eq(v_usize_7_, v_usize_11_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_box(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_eq(v_ssize_8_, v_ssize_12_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
else
{
uint8_t v_relaxedReuse_22_; 
v_relaxedReuse_22_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*2);
if (v_relaxedReuse_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_23_ = l_Lean_Name_getPrefix(v_name_5_);
v___x_24_ = l_Lean_Name_getPrefix(v_name_9_);
v___x_25_ = lean_name_eq(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_box(v_relaxedReuse_22_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg___boxed(lean_object* v_c_u2081_30_, lean_object* v_c_u2082_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_30_, v_c_u2082_31_, v_a_32_);
lean_dec_ref(v_a_32_);
lean_dec_ref(v_c_u2082_31_);
lean_dec_ref(v_c_u2081_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(lean_object* v_c_u2081_35_, lean_object* v_c_u2082_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_c_u2081_35_, v_c_u2082_36_, v_a_37_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___boxed(lean_object* v_c_u2081_44_, lean_object* v_c_u2082_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse(v_c_u2081_44_, v_c_u2082_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec_ref(v_c_u2082_45_);
lean_dec_ref(v_c_u2081_44_);
return v_res_52_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object* v_msg_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_56_ = lean_panic_fn_borrowed(v___x_55_, v_msg_54_);
return v___x_56_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_instMonadEIO___redArg();
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object* v_msg_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toApplicative_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_106_; 
v___x_67_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_68_ = l_StateRefT_x27_instMonad___redArg(v___x_67_);
v_toApplicative_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_68_, 1);
lean_dec(v_unused_107_);
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_106_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_toApplicative_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_106_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_toFunctor_73_; lean_object* v_toSeq_74_; lean_object* v_toSeqLeft_75_; lean_object* v_toSeqRight_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_104_; 
v_toFunctor_73_ = lean_ctor_get(v_toApplicative_69_, 0);
v_toSeq_74_ = lean_ctor_get(v_toApplicative_69_, 2);
v_toSeqLeft_75_ = lean_ctor_get(v_toApplicative_69_, 3);
v_toSeqRight_76_ = lean_ctor_get(v_toApplicative_69_, 4);
v_isSharedCheck_104_ = !lean_is_exclusive(v_toApplicative_69_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_dec(v_unused_105_);
v___x_78_ = v_toApplicative_69_;
v_isShared_79_ = v_isSharedCheck_104_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_toSeqRight_76_);
lean_inc(v_toSeqLeft_75_);
lean_inc(v_toSeq_74_);
lean_inc(v_toFunctor_73_);
lean_dec(v_toApplicative_69_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_104_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_89_; 
v___f_80_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_81_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_73_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_73_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_73_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___f_82_);
lean_ctor_set(v___x_84_, 1, v___f_83_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toSeqRight_76_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeqLeft_75_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeq_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 4, v___f_85_);
lean_ctor_set(v___x_78_, 3, v___f_86_);
lean_ctor_set(v___x_78_, 2, v___f_87_);
lean_ctor_set(v___x_78_, 1, v___f_80_);
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_89_ = v___x_78_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___f_80_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v___f_85_);
v___x_89_ = v_reuseFailAlloc_103_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___f_81_);
lean_ctor_set(v___x_71_, 0, v___x_89_);
v___x_91_ = v___x_71_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___f_81_);
v___x_91_ = v_reuseFailAlloc_102_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_3636__overap_100_; lean_object* v___x_101_; 
v___x_92_ = l_StateRefT_x27_instMonad___redArg(v___x_91_);
v___x_93_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_94_ = 0;
v___x_95_ = lean_box(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_93_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = l_instInhabitedOfMonad___redArg(v___x_92_, v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_98_, 0, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_99_, 0, v___f_98_);
v___x_3636__overap_100_ = lean_panic_fn_borrowed(v___f_99_, v_msg_60_);
lean_dec_ref(v___f_99_);
lean_inc(v___y_65_);
lean_inc_ref(v___y_64_);
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc_ref(v___y_61_);
v___x_101_ = lean_apply_6(v___x_3636__overap_100_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, lean_box(0));
return v___x_101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
v___x_121_ = lean_unbox(v___x_120_);
if (v___x_121_ == 0)
{
size_t v___x_122_; size_t v___x_123_; 
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_add(v_i_117_, v___x_122_);
v_i_117_ = v___x_123_;
goto _start;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_unbox(v___x_120_);
return v___x_125_;
}
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object* v_as_127_, lean_object* v_i_128_, lean_object* v_stop_129_){
_start:
{
size_t v_i_boxed_130_; size_t v_stop_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_i_boxed_130_ = lean_unbox_usize(v_i_128_);
lean_dec(v_i_128_);
v_stop_boxed_131_ = lean_unbox_usize(v_stop_129_);
lean_dec(v_stop_129_);
v_res_132_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_127_, v_i_boxed_130_, v_stop_boxed_131_);
lean_dec_ref(v_as_127_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_138_ = lean_unsigned_to_nat(9u);
v___x_139_ = lean_unsigned_to_nat(642u);
v___x_140_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1));
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0));
v___x_142_ = l_mkPanicMessageWithDecl(v___x_141_, v___x_140_, v___x_139_, v___x_138_, v___x_137_);
return v___x_142_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_145_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_146_ = lean_unsigned_to_nat(61u);
v___x_147_ = lean_unsigned_to_nat(125u);
v___x_148_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5));
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_150_ = l_mkPanicMessageWithDecl(v___x_149_, v___x_148_, v___x_147_, v___x_146_, v___x_145_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object* v_info_151_, lean_object* v_w_152_, lean_object* v_c_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___y_161_; lean_object* v___y_162_; lean_object* v_k_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; 
switch(lean_obj_tag(v_c_153_))
{
case 0:
{
lean_object* v_decl_387_; lean_object* v_value_388_; 
v_decl_387_ = lean_ctor_get(v_c_153_, 0);
lean_inc_ref(v_decl_387_);
v_value_388_ = lean_ctor_get(v_decl_387_, 3);
lean_inc(v_value_388_);
if (lean_obj_tag(v_value_388_) == 5)
{
lean_object* v_k_389_; lean_object* v_fvarId_390_; lean_object* v_binderName_391_; lean_object* v_type_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_447_; 
v_k_389_ = lean_ctor_get(v_c_153_, 1);
v_fvarId_390_ = lean_ctor_get(v_decl_387_, 0);
v_binderName_391_ = lean_ctor_get(v_decl_387_, 1);
v_type_392_ = lean_ctor_get(v_decl_387_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_decl_387_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_decl_387_, 3);
lean_dec(v_unused_448_);
v___x_394_ = v_decl_387_;
v_isShared_395_ = v_isSharedCheck_447_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_type_392_);
lean_inc(v_binderName_391_);
lean_inc(v_fvarId_390_);
lean_dec(v_decl_387_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_447_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_i_396_; lean_object* v_args_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_446_; 
v_i_396_ = lean_ctor_get(v_value_388_, 0);
v_args_397_ = lean_ctor_get(v_value_388_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_value_388_);
if (v_isSharedCheck_446_ == 0)
{
v___x_399_ = v_value_388_;
v_isShared_400_ = v_isSharedCheck_446_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_args_397_);
lean_inc(v_i_396_);
lean_dec(v_value_388_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_446_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; lean_object* v___x_403_; 
v___x_401_ = 1;
lean_inc_ref(v_args_397_);
lean_inc_ref(v_i_396_);
if (v_isShared_400_ == 0)
{
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_i_396_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_args_397_);
v___x_403_ = v_reuseFailAlloc_445_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
lean_inc_ref(v_type_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 3, v___x_403_);
v___x_405_ = v___x_394_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fvarId_390_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_binderName_391_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_type_392_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v___x_403_);
v___x_405_ = v_reuseFailAlloc_444_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_info_151_, v_i_396_, v_a_154_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; uint8_t v___y_409_; uint8_t v___x_430_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_430_ = lean_unbox(v_a_407_);
if (v___x_430_ == 0)
{
lean_dec(v_a_407_);
lean_dec_ref(v___x_405_);
lean_dec_ref(v_args_397_);
lean_dec_ref(v_i_396_);
lean_dec_ref(v_type_392_);
lean_inc_ref(v_k_389_);
v_k_167_ = v_k_389_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
else
{
lean_object* v_cidx_431_; lean_object* v_cidx_432_; uint8_t v___x_433_; 
lean_inc_ref(v_k_389_);
lean_dec_ref_known(v_c_153_, 2);
v_cidx_431_ = lean_ctor_get(v_info_151_, 1);
v_cidx_432_ = lean_ctor_get(v_i_396_, 1);
v___x_433_ = lean_nat_dec_eq(v_cidx_431_, v_cidx_432_);
if (v___x_433_ == 0)
{
uint8_t v___x_434_; 
v___x_434_ = lean_unbox(v_a_407_);
v___y_409_ = v___x_434_;
goto v___jp_408_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = 0;
v___y_409_ = v___x_435_;
goto v___jp_408_;
}
}
v___jp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(v___x_410_, 0, v_w_152_);
lean_ctor_set(v___x_410_, 1, v_i_396_);
lean_ctor_set(v___x_410_, 2, v_args_397_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3, v___y_409_);
v___x_411_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_401_, v___x_405_, v_type_392_, v___x_410_, v_a_156_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_a_412_);
lean_ctor_set(v___x_416_, 1, v_k_389_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v_a_407_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_407_);
lean_dec_ref(v_k_389_);
v_a_422_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v___x_405_);
lean_dec_ref(v_args_397_);
lean_dec_ref(v_i_396_);
lean_dec_ref(v_type_392_);
lean_dec_ref_known(v_c_153_, 2);
lean_dec(v_w_152_);
v_a_436_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_406_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_406_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
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
lean_object* v_k_449_; 
lean_dec(v_value_388_);
lean_dec_ref(v_decl_387_);
v_k_449_ = lean_ctor_get(v_c_153_, 1);
lean_inc_ref(v_k_449_);
v_k_167_ = v_k_449_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
}
case 2:
{
lean_object* v_decl_450_; lean_object* v_k_451_; lean_object* v_params_452_; lean_object* v_type_453_; lean_object* v_value_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v_decl_450_ = lean_ctor_get(v_c_153_, 0);
v_k_451_ = lean_ctor_get(v_c_153_, 1);
v_params_452_ = lean_ctor_get(v_decl_450_, 2);
v_type_453_ = lean_ctor_get(v_decl_450_, 3);
v_value_454_ = lean_ctor_get(v_decl_450_, 4);
v___x_455_ = 1;
lean_inc_ref(v_value_454_);
lean_inc(v_w_152_);
v___x_456_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_151_, v_w_152_, v_value_454_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v_snd_458_; uint8_t v___x_459_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v_snd_458_ = lean_ctor_get(v_a_457_, 1);
lean_inc(v_snd_458_);
v___x_459_ = lean_unbox(v_snd_458_);
if (v___x_459_ == 0)
{
lean_dec(v_snd_458_);
lean_dec(v_a_457_);
lean_inc_ref(v_k_451_);
v_k_167_ = v_k_451_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
else
{
lean_object* v_fst_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_w_152_);
v_fst_460_ = lean_ctor_get(v_a_457_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_457_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_a_457_, 1);
lean_dec(v_unused_510_);
v___x_462_ = v_a_457_;
v_isShared_463_ = v_isSharedCheck_509_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_fst_460_);
lean_dec(v_a_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_509_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; 
lean_inc_ref(v_params_452_);
lean_inc_ref(v_type_453_);
lean_inc_ref(v_decl_450_);
v___x_464_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_455_, v_decl_450_, v_type_453_, v_params_452_, v_fst_460_, v_a_156_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_500_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_500_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_500_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_500_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___y_470_; size_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_ptr_addr(v_k_451_);
v___x_478_ = lean_usize_dec_eq(v___x_477_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_inc_ref(v_k_451_);
v_isSharedCheck_485_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; 
v_unused_486_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_487_);
v___x_480_ = v_c_153_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_c_153_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_a_465_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_451_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
v___y_470_ = v___x_483_;
goto v___jp_469_;
}
}
}
else
{
size_t v___x_488_; size_t v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_ptr_addr(v_decl_450_);
v___x_489_ = lean_ptr_addr(v_a_465_);
v___x_490_ = lean_usize_dec_eq(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_inc_ref(v_k_451_);
v_isSharedCheck_497_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_499_);
v___x_492_ = v_c_153_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_dec(v_c_153_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_a_465_);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_451_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
v___y_470_ = v___x_495_;
goto v___jp_469_;
}
}
}
else
{
lean_dec(v_a_465_);
v___y_470_ = v_c_153_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___y_470_);
v___x_472_ = v___x_462_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___y_470_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_458_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_472_);
v___x_474_ = v___x_467_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_462_);
lean_dec(v_snd_458_);
lean_dec_ref_known(v_c_153_, 2);
v_a_501_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_464_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_464_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_c_153_, 2);
lean_dec(v_w_152_);
return v___x_456_;
}
}
case 3:
{
uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_w_152_);
v___x_511_ = 0;
v___x_512_ = lean_box(v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_c_153_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
case 4:
{
lean_object* v_cases_515_; lean_object* v_typeName_516_; lean_object* v_resultType_517_; lean_object* v_discr_518_; lean_object* v_alts_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_571_; 
v_cases_515_ = lean_ctor_get(v_c_153_, 0);
lean_inc_ref(v_cases_515_);
v_typeName_516_ = lean_ctor_get(v_cases_515_, 0);
v_resultType_517_ = lean_ctor_get(v_cases_515_, 1);
v_discr_518_ = lean_ctor_get(v_cases_515_, 2);
v_alts_519_ = lean_ctor_get(v_cases_515_, 3);
v_isSharedCheck_571_ = !lean_is_exclusive(v_cases_515_);
if (v_isSharedCheck_571_ == 0)
{
v___x_521_ = v_cases_515_;
v_isShared_522_ = v_isSharedCheck_571_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_alts_519_);
lean_inc(v_discr_518_);
lean_inc(v_resultType_517_);
lean_inc(v_typeName_516_);
lean_dec(v_cases_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_571_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; 
v_sz_523_ = lean_array_size(v_alts_519_);
v___x_524_ = ((size_t)0ULL);
lean_inc_ref(v_alts_519_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_151_, v_w_152_, v_sz_523_, v___x_524_, v_alts_519_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_562_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_562_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_562_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_562_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___x_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___y_542_; size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_538_ = l_Array_unzip___redArg(v_a_526_);
lean_dec(v_a_526_);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v___x_538_);
v___x_548_ = lean_ptr_addr(v_alts_519_);
lean_dec_ref(v_alts_519_);
v___x_549_ = lean_ptr_addr(v_fst_539_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
v_isSharedCheck_560_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_561_);
v___x_552_ = v_c_153_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_c_153_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 3, v_fst_539_);
v___x_555_ = v___x_521_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_typeName_516_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_resultType_517_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_discr_518_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_fst_539_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v___y_542_ = v___x_557_;
goto v___jp_541_;
}
}
}
}
else
{
lean_dec(v_fst_539_);
lean_del_object(v___x_521_);
lean_dec(v_discr_518_);
lean_dec_ref(v_resultType_517_);
lean_dec(v_typeName_516_);
v___y_542_ = v_c_153_;
goto v___jp_541_;
}
v___jp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = lean_box(v___y_532_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_534_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v_snd_540_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v_snd_540_);
v___y_531_ = v___y_542_;
v___y_532_ = v___x_545_;
goto v___jp_530_;
}
else
{
if (v___x_545_ == 0)
{
lean_dec(v_snd_540_);
v___y_531_ = v___y_542_;
v___y_532_ = v___x_545_;
goto v___jp_530_;
}
else
{
size_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_usize_of_nat(v___x_544_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_540_, v___x_524_, v___x_546_);
lean_dec(v_snd_540_);
v___y_531_ = v___y_542_;
v___y_532_ = v___x_547_;
goto v___jp_530_;
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_521_);
lean_dec_ref(v_alts_519_);
lean_dec(v_discr_518_);
lean_dec_ref(v_resultType_517_);
lean_dec(v_typeName_516_);
lean_dec_ref_known(v_c_153_, 1);
v_a_563_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_525_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_525_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
case 5:
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_w_152_);
v___x_572_ = 0;
v___x_573_ = lean_box(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_c_153_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
case 6:
{
uint8_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_w_152_);
v___x_576_ = 0;
v___x_577_ = lean_box(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_c_153_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
case 8:
{
lean_object* v_k_580_; 
v_k_580_ = lean_ctor_get(v_c_153_, 3);
lean_inc_ref(v_k_580_);
v_k_167_ = v_k_580_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
case 9:
{
lean_object* v_k_581_; 
v_k_581_ = lean_ctor_get(v_c_153_, 5);
lean_inc_ref(v_k_581_);
v_k_167_ = v_k_581_;
v___y_168_ = v_a_154_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
goto v___jp_166_;
}
default: 
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec_ref(v_c_153_);
lean_dec(v_w_152_);
v___x_582_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
v___x_583_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_582_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
return v___x_583_;
}
}
v___jp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(v___y_161_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___y_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
v___jp_166_:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_151_, v_w_152_, v_k_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
switch(lean_obj_tag(v_c_153_))
{
case 0:
{
lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v_decl_177_; lean_object* v_k_178_; size_t v___x_179_; size_t v___x_180_; uint8_t v___x_181_; 
v_fst_175_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_175_);
v_snd_176_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_176_);
lean_dec(v_a_174_);
v_decl_177_ = lean_ctor_get(v_c_153_, 0);
v_k_178_ = lean_ctor_get(v_c_153_, 1);
v___x_179_ = lean_ptr_addr(v_k_178_);
v___x_180_ = lean_ptr_addr(v_fst_175_);
v___x_181_ = lean_usize_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
lean_inc_ref(v_decl_177_);
v_isSharedCheck_189_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_190_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_191_);
v___x_183_ = v_c_153_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_c_153_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_fst_175_);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_decl_177_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_fst_175_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_unbox(v_snd_176_);
lean_dec(v_snd_176_);
v___y_161_ = v___x_187_;
v___y_162_ = v___x_186_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_192_; 
lean_dec(v_fst_175_);
v___x_192_ = lean_unbox(v_snd_176_);
lean_dec(v_snd_176_);
v___y_161_ = v___x_192_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 1:
{
lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v_decl_195_; lean_object* v_k_196_; size_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; 
v_fst_193_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_193_);
v_snd_194_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_194_);
lean_dec(v_a_174_);
v_decl_195_ = lean_ctor_get(v_c_153_, 0);
v_k_196_ = lean_ctor_get(v_c_153_, 1);
v___x_197_ = lean_ptr_addr(v_k_196_);
v___x_198_ = lean_ptr_addr(v_fst_193_);
v___x_199_ = lean_usize_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_decl_195_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_208_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_209_);
v___x_201_ = v_c_153_;
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_c_153_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_207_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 1, v_fst_193_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_decl_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_fst_193_);
v___x_204_ = v_reuseFailAlloc_206_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
uint8_t v___x_205_; 
v___x_205_ = lean_unbox(v_snd_194_);
lean_dec(v_snd_194_);
v___y_161_ = v___x_205_;
v___y_162_ = v___x_204_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_210_; 
lean_dec(v_fst_193_);
v___x_210_ = lean_unbox(v_snd_194_);
lean_dec(v_snd_194_);
v___y_161_ = v___x_210_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 2:
{
lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v_decl_213_; lean_object* v_k_214_; size_t v___x_215_; size_t v___x_216_; uint8_t v___x_217_; 
v_fst_211_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_211_);
v_snd_212_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_212_);
lean_dec(v_a_174_);
v_decl_213_ = lean_ctor_get(v_c_153_, 0);
v_k_214_ = lean_ctor_get(v_c_153_, 1);
v___x_215_ = lean_ptr_addr(v_k_214_);
v___x_216_ = lean_ptr_addr(v_fst_211_);
v___x_217_ = lean_usize_dec_eq(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
lean_inc_ref(v_decl_213_);
v_isSharedCheck_225_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_226_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_227_);
v___x_219_ = v_c_153_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_c_153_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v_fst_211_);
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_decl_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_fst_211_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
uint8_t v___x_223_; 
v___x_223_ = lean_unbox(v_snd_212_);
lean_dec(v_snd_212_);
v___y_161_ = v___x_223_;
v___y_162_ = v___x_222_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_228_; 
lean_dec(v_fst_211_);
v___x_228_ = lean_unbox(v_snd_212_);
lean_dec(v_snd_212_);
v___y_161_ = v___x_228_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 7:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v_fvarId_231_; lean_object* v_i_232_; lean_object* v_y_233_; lean_object* v_k_234_; size_t v___x_235_; size_t v___x_236_; uint8_t v___x_237_; 
v_fst_229_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_229_);
v_snd_230_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_230_);
lean_dec(v_a_174_);
v_fvarId_231_ = lean_ctor_get(v_c_153_, 0);
v_i_232_ = lean_ctor_get(v_c_153_, 1);
v_y_233_ = lean_ctor_get(v_c_153_, 2);
v_k_234_ = lean_ctor_get(v_c_153_, 3);
v___x_235_ = lean_ptr_addr(v_k_234_);
v___x_236_ = lean_ptr_addr(v_fst_229_);
v___x_237_ = lean_usize_dec_eq(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
lean_inc(v_y_233_);
lean_inc(v_i_232_);
lean_inc(v_fvarId_231_);
v_isSharedCheck_245_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_246_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_249_);
v___x_239_ = v_c_153_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_c_153_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 3, v_fst_229_);
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_fvarId_231_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_i_232_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_y_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_fst_229_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_snd_230_);
lean_dec(v_snd_230_);
v___y_161_ = v___x_243_;
v___y_162_ = v___x_242_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_250_; 
lean_dec(v_fst_229_);
v___x_250_ = lean_unbox(v_snd_230_);
lean_dec(v_snd_230_);
v___y_161_ = v___x_250_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 9:
{
lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v_fvarId_253_; lean_object* v_i_254_; lean_object* v_offset_255_; lean_object* v_y_256_; lean_object* v_ty_257_; lean_object* v_k_258_; size_t v___x_259_; size_t v___x_260_; uint8_t v___x_261_; 
v_fst_251_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_251_);
v_snd_252_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_252_);
lean_dec(v_a_174_);
v_fvarId_253_ = lean_ctor_get(v_c_153_, 0);
v_i_254_ = lean_ctor_get(v_c_153_, 1);
v_offset_255_ = lean_ctor_get(v_c_153_, 2);
v_y_256_ = lean_ctor_get(v_c_153_, 3);
v_ty_257_ = lean_ctor_get(v_c_153_, 4);
v_k_258_ = lean_ctor_get(v_c_153_, 5);
v___x_259_ = lean_ptr_addr(v_k_258_);
v___x_260_ = lean_ptr_addr(v_fst_251_);
v___x_261_ = lean_usize_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
lean_inc_ref(v_ty_257_);
lean_inc(v_y_256_);
lean_inc(v_offset_255_);
lean_inc(v_i_254_);
lean_inc(v_fvarId_253_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; 
v_unused_270_ = lean_ctor_get(v_c_153_, 5);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_c_153_, 4);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_275_);
v___x_263_ = v_c_153_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_c_153_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 5, v_fst_251_);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_fvarId_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_i_254_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_offset_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_y_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_ty_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 5, v_fst_251_);
v___x_266_ = v_reuseFailAlloc_268_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
uint8_t v___x_267_; 
v___x_267_ = lean_unbox(v_snd_252_);
lean_dec(v_snd_252_);
v___y_161_ = v___x_267_;
v___y_162_ = v___x_266_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_276_; 
lean_dec(v_fst_251_);
v___x_276_ = lean_unbox(v_snd_252_);
lean_dec(v_snd_252_);
v___y_161_ = v___x_276_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 8:
{
lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v_fvarId_279_; lean_object* v_i_280_; lean_object* v_y_281_; lean_object* v_k_282_; size_t v___x_283_; size_t v___x_284_; uint8_t v___x_285_; 
v_fst_277_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_277_);
v_snd_278_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_278_);
lean_dec(v_a_174_);
v_fvarId_279_ = lean_ctor_get(v_c_153_, 0);
v_i_280_ = lean_ctor_get(v_c_153_, 1);
v_y_281_ = lean_ctor_get(v_c_153_, 2);
v_k_282_ = lean_ctor_get(v_c_153_, 3);
v___x_283_ = lean_ptr_addr(v_k_282_);
v___x_284_ = lean_ptr_addr(v_fst_277_);
v___x_285_ = lean_usize_dec_eq(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
lean_inc(v_y_281_);
lean_inc(v_i_280_);
lean_inc(v_fvarId_279_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_294_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_297_);
v___x_287_ = v_c_153_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_c_153_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 3, v_fst_277_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fvarId_279_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_i_280_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_y_281_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_fst_277_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
uint8_t v___x_291_; 
v___x_291_ = lean_unbox(v_snd_278_);
lean_dec(v_snd_278_);
v___y_161_ = v___x_291_;
v___y_162_ = v___x_290_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_298_; 
lean_dec(v_fst_277_);
v___x_298_ = lean_unbox(v_snd_278_);
lean_dec(v_snd_278_);
v___y_161_ = v___x_298_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 10:
{
lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v_fvarId_301_; lean_object* v_cidx_302_; lean_object* v_k_303_; size_t v___x_304_; size_t v___x_305_; uint8_t v___x_306_; 
v_fst_299_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_299_);
v_snd_300_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_300_);
lean_dec(v_a_174_);
v_fvarId_301_ = lean_ctor_get(v_c_153_, 0);
v_cidx_302_ = lean_ctor_get(v_c_153_, 1);
v_k_303_ = lean_ctor_get(v_c_153_, 2);
v___x_304_ = lean_ptr_addr(v_k_303_);
v___x_305_ = lean_ptr_addr(v_fst_299_);
v___x_306_ = lean_usize_dec_eq(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_cidx_302_);
lean_inc(v_fvarId_301_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_315_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_317_);
v___x_308_ = v_c_153_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_c_153_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 2, v_fst_299_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_fvarId_301_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_cidx_302_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_fst_299_);
v___x_311_ = v_reuseFailAlloc_313_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
uint8_t v___x_312_; 
v___x_312_ = lean_unbox(v_snd_300_);
lean_dec(v_snd_300_);
v___y_161_ = v___x_312_;
v___y_162_ = v___x_311_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_318_; 
lean_dec(v_fst_299_);
v___x_318_ = lean_unbox(v_snd_300_);
lean_dec(v_snd_300_);
v___y_161_ = v___x_318_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 11:
{
lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v_fvarId_321_; lean_object* v_n_322_; uint8_t v_check_323_; uint8_t v_persistent_324_; lean_object* v_k_325_; size_t v___x_326_; size_t v___x_327_; uint8_t v___x_328_; 
v_fst_319_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_319_);
v_snd_320_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_320_);
lean_dec(v_a_174_);
v_fvarId_321_ = lean_ctor_get(v_c_153_, 0);
v_n_322_ = lean_ctor_get(v_c_153_, 1);
v_check_323_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*3);
v_persistent_324_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*3 + 1);
v_k_325_ = lean_ctor_get(v_c_153_, 2);
v___x_326_ = lean_ptr_addr(v_k_325_);
v___x_327_ = lean_ptr_addr(v_fst_319_);
v___x_328_ = lean_usize_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
lean_inc(v_n_322_);
lean_inc(v_fvarId_321_);
v_isSharedCheck_336_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; lean_object* v_unused_338_; lean_object* v_unused_339_; 
v_unused_337_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_339_);
v___x_330_ = v_c_153_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_c_153_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 2, v_fst_319_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_fvarId_321_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_n_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_fst_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*3, v_check_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_335_, sizeof(void*)*3 + 1, v_persistent_324_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
uint8_t v___x_334_; 
v___x_334_ = lean_unbox(v_snd_320_);
lean_dec(v_snd_320_);
v___y_161_ = v___x_334_;
v___y_162_ = v___x_333_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_340_; 
lean_dec(v_fst_319_);
v___x_340_ = lean_unbox(v_snd_320_);
lean_dec(v_snd_320_);
v___y_161_ = v___x_340_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 12:
{
lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v_fvarId_343_; lean_object* v_n_344_; uint8_t v_check_345_; uint8_t v_persistent_346_; lean_object* v_objs_x3f_347_; lean_object* v_k_348_; size_t v___x_349_; size_t v___x_350_; uint8_t v___x_351_; 
v_fst_341_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_341_);
v_snd_342_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_342_);
lean_dec(v_a_174_);
v_fvarId_343_ = lean_ctor_get(v_c_153_, 0);
v_n_344_ = lean_ctor_get(v_c_153_, 1);
v_check_345_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*4);
v_persistent_346_ = lean_ctor_get_uint8(v_c_153_, sizeof(void*)*4 + 1);
v_objs_x3f_347_ = lean_ctor_get(v_c_153_, 2);
v_k_348_ = lean_ctor_get(v_c_153_, 3);
v___x_349_ = lean_ptr_addr(v_k_348_);
v___x_350_ = lean_ptr_addr(v_fst_341_);
v___x_351_ = lean_usize_dec_eq(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
lean_inc(v_objs_x3f_347_);
lean_inc(v_n_344_);
lean_inc(v_fvarId_343_);
v_isSharedCheck_359_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_360_ = lean_ctor_get(v_c_153_, 3);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_c_153_, 2);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_363_);
v___x_353_ = v_c_153_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_c_153_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 3, v_fst_341_);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_fvarId_343_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_n_344_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_objs_x3f_347_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_fst_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*4, v_check_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*4 + 1, v_persistent_346_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
uint8_t v___x_357_; 
v___x_357_ = lean_unbox(v_snd_342_);
lean_dec(v_snd_342_);
v___y_161_ = v___x_357_;
v___y_162_ = v___x_356_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_364_; 
lean_dec(v_fst_341_);
v___x_364_ = lean_unbox(v_snd_342_);
lean_dec(v_snd_342_);
v___y_161_ = v___x_364_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
case 13:
{
lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v_fvarId_367_; lean_object* v_k_368_; size_t v___x_369_; size_t v___x_370_; uint8_t v___x_371_; 
v_fst_365_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_365_);
v_snd_366_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_366_);
lean_dec(v_a_174_);
v_fvarId_367_ = lean_ctor_get(v_c_153_, 0);
v_k_368_ = lean_ctor_get(v_c_153_, 1);
v___x_369_ = lean_ptr_addr(v_k_368_);
v___x_370_ = lean_ptr_addr(v_fst_365_);
v___x_371_ = lean_usize_dec_eq(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
lean_inc(v_fvarId_367_);
v_isSharedCheck_379_ = !lean_is_exclusive(v_c_153_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_380_ = lean_ctor_get(v_c_153_, 1);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_c_153_, 0);
lean_dec(v_unused_381_);
v___x_373_ = v_c_153_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_dec(v_c_153_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 1, v_fst_365_);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_fvarId_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_fst_365_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
uint8_t v___x_377_; 
v___x_377_ = lean_unbox(v_snd_366_);
lean_dec(v_snd_366_);
v___y_161_ = v___x_377_;
v___y_162_ = v___x_376_;
goto v___jp_160_;
}
}
}
else
{
uint8_t v___x_382_; 
lean_dec(v_fst_365_);
v___x_382_ = lean_unbox(v_snd_366_);
lean_dec(v_snd_366_);
v___y_161_ = v___x_382_;
v___y_162_ = v_c_153_;
goto v___jp_160_;
}
}
default: 
{
lean_object* v_snd_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_dec_ref(v_c_153_);
v_snd_383_ = lean_ctor_get(v_a_174_, 1);
lean_inc(v_snd_383_);
lean_dec(v_a_174_);
v___x_384_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
v___x_385_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(v___x_384_);
v___x_386_ = lean_unbox(v_snd_383_);
lean_dec(v_snd_383_);
v___y_161_ = v___x_386_;
v___y_162_ = v___x_385_;
goto v___jp_160_;
}
}
}
else
{
lean_dec_ref(v_c_153_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* v_info_584_, lean_object* v_w_585_, size_t v_sz_586_, size_t v_i_587_, lean_object* v_bs_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_lt(v_i_587_, v_sz_586_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec(v_w_585_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_bs_588_);
return v___x_596_;
}
else
{
lean_object* v_v_597_; lean_object* v___x_598_; lean_object* v_bs_x27_599_; lean_object* v___y_601_; 
v_v_597_ = lean_array_uget(v_bs_588_, v_i_587_);
v___x_598_ = lean_unsigned_to_nat(0u);
v_bs_x27_599_ = lean_array_uset(v_bs_588_, v_i_587_, v___x_598_);
switch(lean_obj_tag(v_v_597_))
{
case 0:
{
lean_object* v_code_626_; 
v_code_626_ = lean_ctor_get(v_v_597_, 2);
lean_inc_ref(v_code_626_);
v___y_601_ = v_code_626_;
goto v___jp_600_;
}
case 1:
{
lean_object* v_code_627_; 
v_code_627_ = lean_ctor_get(v_v_597_, 1);
lean_inc_ref(v_code_627_);
v___y_601_ = v_code_627_;
goto v___jp_600_;
}
default: 
{
lean_object* v_code_628_; 
v_code_628_ = lean_ctor_get(v_v_597_, 0);
lean_inc_ref(v_code_628_);
v___y_601_ = v_code_628_;
goto v___jp_600_;
}
}
v___jp_600_:
{
lean_object* v___x_602_; 
lean_inc(v_w_585_);
v___x_602_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_584_, v_w_585_, v___y_601_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_fst_604_ = lean_ctor_get(v_a_603_, 0);
v_snd_605_ = lean_ctor_get(v_a_603_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_617_ == 0)
{
v___x_607_ = v_a_603_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v_a_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_597_, v_fst_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_snd_605_);
v___x_611_ = v_reuseFailAlloc_616_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_587_, v___x_612_);
v___x_614_ = lean_array_uset(v_bs_x27_599_, v_i_587_, v___x_611_);
v_i_587_ = v___x_613_;
v_bs_588_ = v___x_614_;
goto _start;
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_bs_x27_599_);
lean_dec(v_v_597_);
lean_dec(v_w_585_);
v_a_618_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_602_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_602_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* v_info_629_, lean_object* v_w_630_, lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_bs_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_641_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_629_, v_w_630_, v_sz_boxed_640_, v_i_boxed_641_, v_bs_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v_info_629_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* v_info_643_, lean_object* v_w_644_, lean_object* v_c_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_643_, v_w_644_, v_c_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_info_643_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; lean_object* v_ngen_656_; lean_object* v_namePrefix_657_; lean_object* v_idx_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_687_; 
v___x_655_ = lean_st_ref_get(v___y_653_);
v_ngen_656_ = lean_ctor_get(v___x_655_, 2);
lean_inc_ref(v_ngen_656_);
lean_dec(v___x_655_);
v_namePrefix_657_ = lean_ctor_get(v_ngen_656_, 0);
v_idx_658_ = lean_ctor_get(v_ngen_656_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_ngen_656_);
if (v_isSharedCheck_687_ == 0)
{
v___x_660_ = v_ngen_656_;
v_isShared_661_ = v_isSharedCheck_687_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_idx_658_);
lean_inc(v_namePrefix_657_);
lean_dec(v_ngen_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_687_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_r_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_idx_658_);
lean_inc(v_namePrefix_657_);
v_r_662_ = l_Lean_Name_num___override(v_namePrefix_657_, v_idx_658_);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_idx_658_, v___x_663_);
lean_dec(v_idx_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_namePrefix_657_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_664_);
v___x_666_ = v_reuseFailAlloc_686_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v_env_668_; lean_object* v_nextMacroScope_669_; lean_object* v_auxDeclNGen_670_; lean_object* v_traceState_671_; lean_object* v_cache_672_; lean_object* v_messages_673_; lean_object* v_infoState_674_; lean_object* v_snapshotTasks_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_684_; 
v___x_667_ = lean_st_ref_take(v___y_653_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
v_nextMacroScope_669_ = lean_ctor_get(v___x_667_, 1);
v_auxDeclNGen_670_ = lean_ctor_get(v___x_667_, 3);
v_traceState_671_ = lean_ctor_get(v___x_667_, 4);
v_cache_672_ = lean_ctor_get(v___x_667_, 5);
v_messages_673_ = lean_ctor_get(v___x_667_, 6);
v_infoState_674_ = lean_ctor_get(v___x_667_, 7);
v_snapshotTasks_675_ = lean_ctor_get(v___x_667_, 8);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v___x_667_, 2);
lean_dec(v_unused_685_);
v___x_677_ = v___x_667_;
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snapshotTasks_675_);
lean_inc(v_infoState_674_);
lean_inc(v_messages_673_);
lean_inc(v_cache_672_);
lean_inc(v_traceState_671_);
lean_inc(v_auxDeclNGen_670_);
lean_inc(v_nextMacroScope_669_);
lean_inc(v_env_668_);
lean_dec(v___x_667_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v___x_666_);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_env_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_nextMacroScope_669_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_auxDeclNGen_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_traceState_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v_cache_672_);
lean_ctor_set(v_reuseFailAlloc_683_, 6, v_messages_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 7, v_infoState_674_);
lean_ctor_set(v_reuseFailAlloc_683_, 8, v_snapshotTasks_675_);
v___x_680_ = v_reuseFailAlloc_683_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_st_ref_put(v___y_653_, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_r_662_);
return v___x_682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_688_);
lean_dec(v___y_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v___x_697_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_695_);
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_712_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_box(0);
v___x_720_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
v___x_721_ = l_Lean_Expr_const___override(v___x_720_, v___x_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* v_x_722_, lean_object* v_info_723_, lean_object* v_c_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_n(v_a_732_, 2);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_723_, v_a_732_, v_c_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_788_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_788_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_788_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_788_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_snd_738_; uint8_t v___x_739_; 
v_snd_738_ = lean_ctor_get(v_a_734_, 1);
v___x_739_ = lean_unbox(v_snd_738_);
if (v___x_739_ == 0)
{
lean_object* v_fst_740_; lean_object* v___x_742_; 
lean_dec(v_a_732_);
lean_dec(v_x_722_);
v_fst_740_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_fst_740_);
lean_dec(v_a_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_fst_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v_fst_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_786_; 
lean_del_object(v___x_736_);
v_fst_744_ = lean_ctor_get(v_a_734_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_a_734_, 1);
lean_dec(v_unused_787_);
v___x_746_ = v_a_734_;
v_isShared_747_ = v_isSharedCheck_786_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_fst_744_);
lean_dec(v_a_734_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_786_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
v___x_749_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_748_, v_a_727_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_777_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_777_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_777_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_777_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_size_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v_size_754_ = lean_ctor_get(v_info_723_, 2);
v___x_755_ = 1;
v___x_756_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
lean_inc(v_size_754_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 11);
lean_ctor_set(v___x_746_, 1, v_x_722_);
lean_ctor_set(v___x_746_, 0, v_size_754_);
v___x_758_ = v___x_746_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_size_754_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_x_722_);
v___x_758_ = v_reuseFailAlloc_776_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_lctx_761_; lean_object* v_nextIdx_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_775_; 
v___x_759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_759_, 0, v_a_732_);
lean_ctor_set(v___x_759_, 1, v_a_750_);
lean_ctor_set(v___x_759_, 2, v___x_756_);
lean_ctor_set(v___x_759_, 3, v___x_758_);
v___x_760_ = lean_st_ref_take(v_a_727_);
v_lctx_761_ = lean_ctor_get(v___x_760_, 0);
v_nextIdx_762_ = lean_ctor_get(v___x_760_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_775_ == 0)
{
v___x_764_ = v___x_760_;
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_nextIdx_762_);
lean_inc(v_lctx_761_);
lean_dec(v___x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_inc_ref(v___x_759_);
v___x_766_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_755_, v_lctx_761_, v___x_759_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_nextIdx_762_);
v___x_768_ = v_reuseFailAlloc_774_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_769_ = lean_st_ref_put(v_a_727_, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_759_);
lean_ctor_set(v___x_770_, 1, v_fst_744_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_770_);
v___x_772_ = v___x_752_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_746_);
lean_dec(v_fst_744_);
lean_dec(v_a_732_);
lean_dec(v_x_722_);
v_a_778_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_749_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_749_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_a_732_);
lean_dec(v_x_722_);
v_a_789_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_733_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_733_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_c_724_);
lean_dec(v_x_722_);
v_a_797_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_731_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_731_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* v_x_805_, lean_object* v_info_806_, lean_object* v_c_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_805_, v_info_806_, v_c_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_info_806_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_828_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* v_x_829_, lean_object* v_as_830_, size_t v_i_831_, size_t v_stop_832_){
_start:
{
uint8_t v___x_833_; 
v___x_833_ = lean_usize_dec_eq(v_i_831_, v_stop_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_array_uget_borrowed(v_as_830_, v_i_831_);
v___x_835_ = 1;
lean_inc(v_x_829_);
v___x_836_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_829_);
v___x_837_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_835_, v___x_834_, v___x_836_);
lean_dec(v___x_836_);
if (v___x_837_ == 0)
{
size_t v___x_838_; size_t v___x_839_; 
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_i_831_, v___x_838_);
v_i_831_ = v___x_839_;
goto _start;
}
else
{
lean_dec(v_x_829_);
return v___x_837_;
}
}
else
{
uint8_t v___x_841_; 
lean_dec(v_x_829_);
v___x_841_ = 0;
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* v_x_842_, lean_object* v_as_843_, lean_object* v_i_844_, lean_object* v_stop_845_){
_start:
{
size_t v_i_boxed_846_; size_t v_stop_boxed_847_; uint8_t v_res_848_; lean_object* v_r_849_; 
v_i_boxed_846_ = lean_unbox_usize(v_i_844_);
lean_dec(v_i_844_);
v_stop_boxed_847_ = lean_unbox_usize(v_stop_845_);
lean_dec(v_stop_845_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_842_, v_as_843_, v_i_boxed_846_, v_stop_boxed_847_);
lean_dec_ref(v_as_843_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* v_instr_850_, lean_object* v_x_851_){
_start:
{
if (lean_obj_tag(v_instr_850_) == 0)
{
lean_object* v_decl_852_; lean_object* v_value_853_; 
v_decl_852_ = lean_ctor_get(v_instr_850_, 0);
v_value_853_ = lean_ctor_get(v_decl_852_, 3);
if (lean_obj_tag(v_value_853_) == 5)
{
lean_object* v_args_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_args_854_ = lean_ctor_get(v_value_853_, 1);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_array_get_size(v_args_854_);
v___x_857_ = lean_nat_dec_lt(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_dec(v_x_851_);
return v___x_857_;
}
else
{
if (v___x_857_ == 0)
{
lean_dec(v_x_851_);
return v___x_857_;
}
else
{
size_t v___x_858_; size_t v___x_859_; uint8_t v___x_860_; 
v___x_858_ = ((size_t)0ULL);
v___x_859_ = lean_usize_of_nat(v___x_856_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_851_, v_args_854_, v___x_858_, v___x_859_);
return v___x_860_;
}
}
}
else
{
uint8_t v___x_861_; 
lean_dec(v_x_851_);
v___x_861_ = 0;
return v___x_861_;
}
}
else
{
uint8_t v___x_862_; 
lean_dec(v_x_851_);
v___x_862_ = 0;
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* v_instr_863_, lean_object* v_x_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_863_, v_x_864_);
lean_dec_ref(v_instr_863_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t v_x_867_){
_start:
{
switch(v_x_867_)
{
case 0:
{
lean_object* v___x_868_; 
v___x_868_ = lean_unsigned_to_nat(0u);
return v___x_868_;
}
case 1:
{
lean_object* v___x_869_; 
v___x_869_ = lean_unsigned_to_nat(1u);
return v___x_869_;
}
default: 
{
lean_object* v___x_870_; 
v___x_870_ = lean_unsigned_to_nat(2u);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object* v_x_871_){
_start:
{
uint8_t v_x_boxed_872_; lean_object* v_res_873_; 
v_x_boxed_872_ = lean_unbox(v_x_871_);
v_res_873_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_boxed_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* v_k_874_){
_start:
{
lean_inc(v_k_874_);
return v_k_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* v_k_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_875_);
lean_dec(v_k_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* v_motive_877_, lean_object* v_ctorIdx_878_, uint8_t v_t_879_, lean_object* v_h_880_, lean_object* v_k_881_){
_start:
{
lean_inc(v_k_881_);
return v_k_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* v_motive_882_, lean_object* v_ctorIdx_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_k_886_){
_start:
{
uint8_t v_t_boxed_887_; lean_object* v_res_888_; 
v_t_boxed_887_ = lean_unbox(v_t_884_);
v_res_888_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(v_motive_882_, v_ctorIdx_883_, v_t_boxed_887_, v_h_885_, v_k_886_);
lean_dec(v_k_886_);
lean_dec(v_ctorIdx_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* v_ownedArg_889_){
_start:
{
lean_inc(v_ownedArg_889_);
return v_ownedArg_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* v_ownedArg_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_890_);
lean_dec(v_ownedArg_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* v_motive_892_, uint8_t v_t_893_, lean_object* v_h_894_, lean_object* v_ownedArg_895_){
_start:
{
lean_inc(v_ownedArg_895_);
return v_ownedArg_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* v_motive_896_, lean_object* v_t_897_, lean_object* v_h_898_, lean_object* v_ownedArg_899_){
_start:
{
uint8_t v_t_boxed_900_; lean_object* v_res_901_; 
v_t_boxed_900_ = lean_unbox(v_t_897_);
v_res_901_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_896_, v_t_boxed_900_, v_h_898_, v_ownedArg_899_);
lean_dec(v_ownedArg_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* v_other_902_){
_start:
{
lean_inc(v_other_902_);
return v_other_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* v_other_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_903_);
lean_dec(v_other_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* v_motive_905_, uint8_t v_t_906_, lean_object* v_h_907_, lean_object* v_other_908_){
_start:
{
lean_inc(v_other_908_);
return v_other_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* v_motive_909_, lean_object* v_t_910_, lean_object* v_h_911_, lean_object* v_other_912_){
_start:
{
uint8_t v_t_boxed_913_; lean_object* v_res_914_; 
v_t_boxed_913_ = lean_unbox(v_t_910_);
v_res_914_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_909_, v_t_boxed_913_, v_h_911_, v_other_912_);
lean_dec(v_other_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* v_none_915_){
_start:
{
lean_inc(v_none_915_);
return v_none_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* v_none_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_916_);
lean_dec(v_none_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* v_motive_918_, uint8_t v_t_919_, lean_object* v_h_920_, lean_object* v_none_921_){
_start:
{
lean_inc(v_none_921_);
return v_none_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* v_motive_922_, lean_object* v_t_923_, lean_object* v_h_924_, lean_object* v_none_925_){
_start:
{
uint8_t v_t_boxed_926_; lean_object* v_res_927_; 
v_t_boxed_926_ = lean_unbox(v_t_923_);
v_res_927_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(v_motive_922_, v_t_boxed_926_, v_h_924_, v_none_925_);
lean_dec(v_none_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* v_x_928_, lean_object* v_as_929_, size_t v_sz_930_, size_t v_i_931_, lean_object* v_b_932_){
_start:
{
lean_object* v_a_935_; uint8_t v___x_939_; 
v___x_939_ = lean_usize_dec_lt(v_i_931_, v_sz_930_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_932_);
return v___x_940_;
}
else
{
lean_object* v_snd_941_; lean_object* v_fst_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_986_; 
v_snd_941_ = lean_ctor_get(v_b_932_, 1);
v_fst_942_ = lean_ctor_get(v_b_932_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_b_932_);
if (v_isSharedCheck_986_ == 0)
{
v___x_944_ = v_b_932_;
v_isShared_945_ = v_isSharedCheck_986_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_942_);
lean_dec(v_b_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_986_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_array_946_; lean_object* v_start_947_; lean_object* v_stop_948_; uint8_t v___x_949_; 
v_array_946_ = lean_ctor_get(v_snd_941_, 0);
v_start_947_ = lean_ctor_get(v_snd_941_, 1);
v_stop_948_ = lean_ctor_get(v_snd_941_, 2);
v___x_949_ = lean_nat_dec_lt(v_start_947_, v_stop_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_951_; 
if (v_isShared_945_ == 0)
{
v___x_951_ = v___x_944_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_fst_942_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_snd_941_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
else
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_982_; 
lean_inc(v_stop_948_);
lean_inc(v_start_947_);
lean_inc_ref(v_array_946_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_snd_941_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; 
v_unused_983_ = lean_ctor_get(v_snd_941_, 2);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_snd_941_, 1);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_snd_941_, 0);
lean_dec(v_unused_985_);
v___x_955_ = v_snd_941_;
v_isShared_956_ = v_isSharedCheck_982_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_snd_941_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_982_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_a_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v_a_957_ = lean_array_uget_borrowed(v_as_929_, v_i_931_);
v___x_958_ = lean_array_fget(v_array_946_, v_start_947_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_add(v_start_947_, v___x_959_);
lean_dec(v_start_947_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_960_);
v___x_962_ = v___x_955_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_array_946_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_stop_948_);
v___x_962_ = v_reuseFailAlloc_981_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
uint8_t v___y_964_; 
if (lean_obj_tag(v_a_957_) == 1)
{
lean_object* v_fvarId_969_; uint8_t v___x_970_; 
v_fvarId_969_ = lean_ctor_get(v_a_957_, 0);
v___x_970_ = l_Lean_instBEqFVarId_beq(v_fvarId_969_, v_x_928_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v___x_958_);
lean_del_object(v___x_944_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_fst_942_);
lean_ctor_set(v___x_971_, 1, v___x_962_);
v_a_935_ = v___x_971_;
goto v___jp_934_;
}
else
{
uint8_t v___x_972_; 
v___x_972_ = lean_unbox(v_fst_942_);
switch(v___x_972_)
{
case 0:
{
uint8_t v_borrow_973_; 
v_borrow_973_ = lean_ctor_get_uint8(v___x_958_, sizeof(void*)*3);
lean_dec(v___x_958_);
if (v_borrow_973_ == 0)
{
uint8_t v___x_974_; 
v___x_974_ = lean_unbox(v_fst_942_);
lean_dec(v_fst_942_);
v___y_964_ = v___x_974_;
goto v___jp_963_;
}
else
{
uint8_t v___x_975_; 
lean_dec(v_fst_942_);
v___x_975_ = 1;
v___y_964_ = v___x_975_;
goto v___jp_963_;
}
}
case 1:
{
uint8_t v___x_976_; 
lean_dec(v___x_958_);
v___x_976_ = lean_unbox(v_fst_942_);
lean_dec(v_fst_942_);
v___y_964_ = v___x_976_;
goto v___jp_963_;
}
default: 
{
uint8_t v_borrow_977_; 
lean_dec(v_fst_942_);
v_borrow_977_ = lean_ctor_get_uint8(v___x_958_, sizeof(void*)*3);
lean_dec(v___x_958_);
if (v_borrow_977_ == 0)
{
uint8_t v___x_978_; 
v___x_978_ = 0;
v___y_964_ = v___x_978_;
goto v___jp_963_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = 1;
v___y_964_ = v___x_979_;
goto v___jp_963_;
}
}
}
}
}
else
{
lean_object* v___x_980_; 
lean_dec(v___x_958_);
lean_del_object(v___x_944_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_fst_942_);
lean_ctor_set(v___x_980_, 1, v___x_962_);
v_a_935_ = v___x_980_;
goto v___jp_934_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_box(v___y_964_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_962_);
lean_ctor_set(v___x_944_, 0, v___x_965_);
v___x_967_ = v___x_944_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_a_935_ = v___x_967_;
goto v___jp_934_;
}
}
}
}
}
}
}
v___jp_934_:
{
size_t v___x_936_; size_t v___x_937_; 
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_931_, v___x_936_);
v_i_931_ = v___x_937_;
v_b_932_ = v_a_935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* v_x_987_, lean_object* v_as_988_, lean_object* v_sz_989_, lean_object* v_i_990_, lean_object* v_b_991_, lean_object* v___y_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_989_);
lean_dec(v_sz_989_);
v_i_boxed_994_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_987_, v_as_988_, v_sz_boxed_993_, v_i_boxed_994_, v_b_991_);
lean_dec_ref(v_as_988_);
lean_dec(v_x_987_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* v_instr_996_, lean_object* v_x_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
if (lean_obj_tag(v_instr_996_) == 0)
{
lean_object* v_decl_1014_; lean_object* v_value_1015_; 
v_decl_1014_ = lean_ctor_get(v_instr_996_, 0);
v_value_1015_ = lean_ctor_get(v_decl_1014_, 3);
lean_inc(v_value_1015_);
switch(lean_obj_tag(v_value_1015_))
{
case 9:
{
lean_object* v_fn_1016_; lean_object* v_args_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref_known(v_instr_996_, 1);
v_fn_1016_ = lean_ctor_get(v_value_1015_, 0);
v_args_1017_ = lean_ctor_get(v_value_1015_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_value_1015_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1019_ = v_value_1015_;
v_isShared_1020_ = v_isSharedCheck_1079_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_args_1017_);
lean_inc(v_fn_1016_);
lean_dec(v_value_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1079_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
uint8_t v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = 1;
lean_inc_ref(v_args_1017_);
lean_inc(v_fn_1016_);
if (v_isShared_1020_ == 0)
{
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fn_1016_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_args_1017_);
v___x_1023_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1016_, v_a_1002_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1069_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1069_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1069_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_a_1025_) == 1)
{
lean_object* v_val_1029_; lean_object* v_params_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
v_val_1029_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_a_1025_, 1);
v_params_1030_ = lean_ctor_get(v_val_1029_, 3);
lean_inc_ref(v_params_1030_);
lean_dec(v_val_1029_);
v___x_1031_ = 2;
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_array_get_size(v_params_1030_);
v___x_1034_ = l_Array_toSubarray___redArg(v_params_1030_, v___x_1032_, v___x_1033_);
v___x_1035_ = lean_box(v___x_1031_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1034_);
v_sz_1037_ = lean_array_size(v_args_1017_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_997_, v_args_1017_, v_sz_1037_, v___x_1038_, v___x_1036_);
lean_dec_ref(v_args_1017_);
lean_dec(v_x_997_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_fst_1044_; lean_object* v___x_1046_; 
v_fst_1044_ = lean_ctor_get(v_a_1040_, 0);
lean_inc(v_fst_1044_);
lean_dec(v_a_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_fst_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_a_1049_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1039_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1039_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
lean_dec(v_a_1025_);
lean_dec_ref(v_args_1017_);
v___x_1057_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_997_);
v___x_1058_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1021_, v___x_1023_, v___x_1057_);
lean_dec(v___x_1057_);
lean_dec_ref(v___x_1023_);
if (v___x_1058_ == 0)
{
uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1059_ = 2;
v___x_1060_ = lean_box(v___x_1059_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1060_);
v___x_1062_ = v___x_1027_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1064_ = 0;
v___x_1065_ = lean_box(v___x_1064_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1065_);
v___x_1067_ = v___x_1027_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v___x_1023_);
lean_dec_ref(v_args_1017_);
lean_dec(v_x_997_);
v_a_1070_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1024_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1024_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
case 10:
{
lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1105_; 
v_isSharedCheck_1105_ = !lean_is_exclusive(v_instr_996_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v_instr_996_, 0);
lean_dec(v_unused_1106_);
v___x_1081_ = v_instr_996_;
v_isShared_1082_ = v_isSharedCheck_1105_;
goto v_resetjp_1080_;
}
else
{
lean_dec(v_instr_996_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1105_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_fn_1083_; lean_object* v_args_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1104_; 
v_fn_1083_ = lean_ctor_get(v_value_1015_, 0);
v_args_1084_ = lean_ctor_get(v_value_1015_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_value_1015_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1086_ = v_value_1015_;
v_isShared_1087_ = v_isSharedCheck_1104_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_args_1084_);
lean_inc(v_fn_1083_);
lean_dec(v_value_1015_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1104_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint8_t v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = 1;
if (v_isShared_1087_ == 0)
{
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_fn_1083_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_args_1084_);
v___x_1090_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_997_);
v___x_1092_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1088_, v___x_1090_, v___x_1091_);
lean_dec(v___x_1091_);
lean_dec_ref(v___x_1090_);
if (v___x_1092_ == 0)
{
uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = 2;
v___x_1094_ = lean_box(v___x_1093_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1094_);
v___x_1096_ = v___x_1081_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
else
{
uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1098_ = 0;
v___x_1099_ = lean_box(v___x_1098_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1099_);
v___x_1101_ = v___x_1081_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1132_; 
v_isSharedCheck_1132_ = !lean_is_exclusive(v_instr_996_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_instr_996_, 0);
lean_dec(v_unused_1133_);
v___x_1108_ = v_instr_996_;
v_isShared_1109_ = v_isSharedCheck_1132_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v_instr_996_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1132_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fvarId_1110_; lean_object* v_args_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1131_; 
v_fvarId_1110_ = lean_ctor_get(v_value_1015_, 0);
v_args_1111_ = lean_ctor_get(v_value_1015_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_value_1015_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1113_ = v_value_1015_;
v_isShared_1114_ = v_isSharedCheck_1131_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_args_1111_);
lean_inc(v_fvarId_1110_);
lean_dec(v_value_1015_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1131_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint8_t v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = 1;
if (v_isShared_1114_ == 0)
{
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_fvarId_1110_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_args_1111_);
v___x_1117_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_997_);
v___x_1119_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1115_, v___x_1117_, v___x_1118_);
lean_dec(v___x_1118_);
lean_dec_ref(v___x_1117_);
if (v___x_1119_ == 0)
{
uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = 2;
v___x_1121_ = lean_box(v___x_1120_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1121_);
v___x_1123_ = v___x_1108_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
else
{
uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1125_ = 0;
v___x_1126_ = lean_box(v___x_1125_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1126_);
v___x_1128_ = v___x_1108_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
default: 
{
lean_dec(v_value_1015_);
goto v___jp_1004_;
}
}
}
else
{
goto v___jp_1004_;
}
v___jp_1004_:
{
uint8_t v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = 1;
v___x_1006_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_997_);
v___x_1007_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_1005_, v_instr_996_, v___x_1006_);
lean_dec(v___x_1006_);
lean_dec_ref(v_instr_996_);
if (v___x_1007_ == 0)
{
uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = 2;
v___x_1009_ = lean_box(v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
else
{
uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = 1;
v___x_1012_ = lean_box(v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* v_instr_1134_, lean_object* v_x_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1134_, v_x_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* v_x_1143_, lean_object* v_as_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1143_, v_as_1144_, v_sz_1145_, v_i_1146_, v_b_1147_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* v_x_1155_, lean_object* v_as_1156_, lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1155_, v_as_1156_, v_sz_boxed_1166_, v_i_boxed_1167_, v_b_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec_ref(v_as_1156_);
lean_dec(v_x_1155_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* v_alt_1169_, lean_object* v_f_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___y_1178_; 
switch(lean_obj_tag(v_alt_1169_))
{
case 0:
{
lean_object* v_code_1197_; 
v_code_1197_ = lean_ctor_get(v_alt_1169_, 2);
lean_inc_ref(v_code_1197_);
v___y_1178_ = v_code_1197_;
goto v___jp_1177_;
}
case 1:
{
lean_object* v_code_1198_; 
v_code_1198_ = lean_ctor_get(v_alt_1169_, 1);
lean_inc_ref(v_code_1198_);
v___y_1178_ = v_code_1198_;
goto v___jp_1177_;
}
default: 
{
lean_object* v_code_1199_; 
v_code_1199_ = lean_ctor_get(v_alt_1169_, 0);
lean_inc_ref(v_code_1199_);
v___y_1178_ = v_code_1199_;
goto v___jp_1177_;
}
}
v___jp_1177_:
{
lean_object* v___x_1179_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc_ref(v___y_1171_);
v___x_1179_ = lean_apply_7(v_f_1170_, v___y_1178_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, lean_box(0));
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1169_, v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_alt_1169_);
v_a_1189_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1179_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1179_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* v_alt_1200_, lean_object* v_f_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1200_, v_f_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* v_x_1209_, lean_object* v_info_1210_, lean_object* v_c_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1209_, v_info_1210_, v_c_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v_a_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* v_x_1219_, lean_object* v_info_1220_, lean_object* v_i_1221_, lean_object* v_as_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_array_get_size(v_as_1222_);
v___x_1230_ = lean_nat_dec_lt(v_i_1221_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_i_1221_);
lean_dec_ref(v_info_1220_);
lean_dec(v_x_1219_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_as_1222_);
return v___x_1231_;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_a_1232_ = lean_array_fget_borrowed(v_as_1222_, v_i_1221_);
lean_inc_ref(v_info_1220_);
lean_inc(v_x_1219_);
v___x_1233_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(v___x_1233_, 0, v_x_1219_);
lean_closure_set(v___x_1233_, 1, v_info_1220_);
lean_inc(v_a_1232_);
v___x_1234_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_1232_, v___x_1233_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; size_t v___x_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = lean_ptr_addr(v_a_1232_);
v___x_1237_ = lean_ptr_addr(v_a_1235_);
v___x_1238_ = lean_usize_dec_eq(v___x_1236_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_i_1221_, v___x_1239_);
v___x_1241_ = lean_array_fset(v_as_1222_, v_i_1221_, v_a_1235_);
lean_dec(v_i_1221_);
v_i_1221_ = v___x_1240_;
v_as_1222_ = v___x_1241_;
goto _start;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_a_1235_);
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1221_, v___x_1243_);
lean_dec(v_i_1221_);
v_i_1221_ = v___x_1244_;
goto _start;
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_as_1222_);
lean_dec(v_i_1221_);
lean_dec_ref(v_info_1220_);
lean_dec(v_x_1219_);
v_a_1246_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1234_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1234_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_1256_ = lean_unsigned_to_nat(61u);
v___x_1257_ = lean_unsigned_to_nat(247u);
v___x_1258_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
v___x_1259_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_1260_ = l_mkPanicMessageWithDecl(v___x_1259_, v___x_1258_, v___x_1257_, v___x_1256_, v___x_1255_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* v_x_1261_, lean_object* v_info_1262_, lean_object* v_c_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
switch(lean_obj_tag(v_c_1263_))
{
case 0:
{
lean_object* v_decl_1270_; lean_object* v_k_1271_; uint8_t v___x_1272_; lean_object* v_instr_1273_; uint8_t v___x_1274_; uint8_t v___x_1275_; 
v_decl_1270_ = lean_ctor_get(v_c_1263_, 0);
v_k_1271_ = lean_ctor_get(v_c_1263_, 1);
v___x_1272_ = 1;
v_instr_1273_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1272_, v_c_1263_);
lean_inc(v_x_1261_);
v___x_1274_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1273_, v_x_1261_);
v___x_1275_ = 1;
if (v___x_1274_ == 0)
{
lean_object* v___x_1276_; 
lean_inc_ref(v_k_1271_);
lean_inc_ref(v_info_1262_);
lean_inc(v_x_1261_);
v___x_1276_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1261_, v_info_1262_, v_k_1271_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1394_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1394_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1394_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___y_1282_; lean_object* v_snd_1288_; uint8_t v___x_1289_; 
v_snd_1288_ = lean_ctor_get(v_a_1277_, 1);
v___x_1289_ = lean_unbox(v_snd_1288_);
if (v___x_1289_ == 0)
{
lean_object* v_fst_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1379_; 
lean_inc(v_snd_1288_);
lean_del_object(v___x_1279_);
v_fst_1290_ = lean_ctor_get(v_a_1277_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_1277_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v_a_1277_, 1);
lean_dec(v_unused_1380_);
v___x_1292_ = v_a_1277_;
v_isShared_1293_ = v_isSharedCheck_1379_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_fst_1290_);
lean_dec(v_a_1277_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1379_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; 
lean_inc(v_x_1261_);
v___x_1294_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1273_, v_x_1261_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1370_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1370_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1370_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___y_1300_; lean_object* v___y_1308_; uint8_t v___x_1312_; 
v___x_1312_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
switch(v___x_1312_)
{
case 0:
{
size_t v___x_1313_; size_t v___x_1314_; uint8_t v___x_1315_; 
lean_del_object(v___x_1297_);
lean_del_object(v___x_1292_);
lean_dec(v_snd_1288_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1313_ = lean_ptr_addr(v_k_1271_);
v___x_1314_ = lean_ptr_addr(v_fst_1290_);
v___x_1315_ = lean_usize_dec_eq(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_inc_ref(v_decl_1270_);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; lean_object* v_unused_1324_; 
v_unused_1323_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1324_);
v___x_1317_ = v_c_1263_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v_c_1263_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_fst_1290_);
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_decl_1270_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_fst_1290_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
v___y_1308_ = v___x_1320_;
goto v___jp_1307_;
}
}
}
else
{
lean_dec(v_fst_1290_);
v___y_1308_ = v_c_1263_;
goto v___jp_1307_;
}
}
case 1:
{
lean_object* v___x_1325_; 
lean_del_object(v___x_1297_);
lean_del_object(v___x_1292_);
lean_dec(v_snd_1288_);
v___x_1325_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1261_, v_info_1262_, v_fst_1290_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec_ref(v_info_1262_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1349_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1349_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1349_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___y_1331_; size_t v___x_1337_; size_t v___x_1338_; uint8_t v___x_1339_; 
v___x_1337_ = lean_ptr_addr(v_k_1271_);
v___x_1338_ = lean_ptr_addr(v_a_1326_);
v___x_1339_ = lean_usize_dec_eq(v___x_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_inc_ref(v_decl_1270_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; 
v_unused_1347_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1348_);
v___x_1341_ = v_c_1263_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v_c_1263_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_a_1326_);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_decl_1270_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_a_1326_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
v___y_1331_ = v___x_1344_;
goto v___jp_1330_;
}
}
}
else
{
lean_dec(v_a_1326_);
v___y_1331_ = v_c_1263_;
goto v___jp_1330_;
}
v___jp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1332_ = lean_box(v___x_1275_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___y_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1333_);
v___x_1335_ = v___x_1328_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref_known(v_c_1263_, 2);
v_a_1350_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1325_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1325_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
default: 
{
size_t v___x_1358_; size_t v___x_1359_; uint8_t v___x_1360_; 
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1358_ = lean_ptr_addr(v_k_1271_);
v___x_1359_ = lean_ptr_addr(v_fst_1290_);
v___x_1360_ = lean_usize_dec_eq(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_inc_ref(v_decl_1270_);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1368_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1369_);
v___x_1362_ = v_c_1263_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v_c_1263_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v_fst_1290_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_decl_1270_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_fst_1290_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
v___y_1300_ = v___x_1365_;
goto v___jp_1299_;
}
}
}
else
{
lean_dec(v_fst_1290_);
v___y_1300_ = v_c_1263_;
goto v___jp_1299_;
}
}
}
v___jp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___y_1300_);
v___x_1302_ = v___x_1292_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___y_1300_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_snd_1288_);
v___x_1302_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1304_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1302_);
v___x_1304_ = v___x_1297_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(v___x_1275_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___y_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1292_);
lean_dec(v_fst_1290_);
lean_dec(v_snd_1288_);
lean_dec_ref_known(v_c_1263_, 2);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_a_1371_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1294_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1294_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_fst_1381_; size_t v___x_1382_; size_t v___x_1383_; uint8_t v___x_1384_; 
lean_dec_ref(v_instr_1273_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_fst_1381_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_fst_1381_);
lean_dec(v_a_1277_);
v___x_1382_ = lean_ptr_addr(v_k_1271_);
v___x_1383_ = lean_ptr_addr(v_fst_1381_);
v___x_1384_ = lean_usize_dec_eq(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_inc_ref(v_decl_1270_);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; lean_object* v_unused_1393_; 
v_unused_1392_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1393_);
v___x_1386_ = v_c_1263_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_c_1263_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_fst_1381_);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_decl_1270_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_fst_1381_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
v___y_1282_ = v___x_1389_;
goto v___jp_1281_;
}
}
}
else
{
lean_dec(v_fst_1381_);
v___y_1282_ = v_c_1263_;
goto v___jp_1281_;
}
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1283_ = lean_box(v___x_1275_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___y_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1284_);
v___x_1286_ = v___x_1279_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1273_);
lean_dec_ref_known(v_c_1263_, 2);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
return v___x_1276_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref(v_instr_1273_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1395_ = lean_box(v___x_1275_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_c_1263_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
case 2:
{
lean_object* v_decl_1398_; lean_object* v_k_1399_; lean_object* v___x_1400_; 
v_decl_1398_ = lean_ctor_get(v_c_1263_, 0);
v_k_1399_ = lean_ctor_get(v_c_1263_, 1);
lean_inc_ref(v_k_1399_);
lean_inc_ref(v_info_1262_);
lean_inc(v_x_1261_);
v___x_1400_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1261_, v_info_1262_, v_k_1399_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_fst_1402_; lean_object* v_snd_1403_; lean_object* v_params_1404_; lean_object* v_type_1405_; lean_object* v_value_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v_fst_1402_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_fst_1402_);
v_snd_1403_ = lean_ctor_get(v_a_1401_, 1);
lean_inc(v_snd_1403_);
lean_dec(v_a_1401_);
v_params_1404_ = lean_ctor_get(v_decl_1398_, 2);
v_type_1405_ = lean_ctor_get(v_decl_1398_, 3);
v_value_1406_ = lean_ctor_get(v_decl_1398_, 4);
v___x_1407_ = 1;
lean_inc_ref(v_value_1406_);
v___x_1408_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1261_, v_info_1262_, v_value_1406_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v_fst_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1460_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v_fst_1410_ = lean_ctor_get(v_a_1409_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1409_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_a_1409_, 1);
lean_dec(v_unused_1461_);
v___x_1412_ = v_a_1409_;
v_isShared_1413_ = v_isSharedCheck_1460_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_fst_1410_);
lean_dec(v_a_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1460_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; 
lean_inc_ref(v_params_1404_);
lean_inc_ref(v_type_1405_);
lean_inc_ref(v_decl_1398_);
v___x_1414_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1407_, v_decl_1398_, v_type_1405_, v_params_1404_, v_fst_1410_, v_a_1266_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1451_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1451_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1451_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___y_1420_; size_t v___x_1427_; size_t v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = lean_ptr_addr(v_k_1399_);
v___x_1428_ = lean_ptr_addr(v_fst_1402_);
v___x_1429_ = lean_usize_dec_eq(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; lean_object* v_unused_1438_; 
v_unused_1437_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1438_);
v___x_1431_ = v_c_1263_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v_c_1263_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_fst_1402_);
lean_ctor_set(v___x_1431_, 0, v_a_1415_);
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1415_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_fst_1402_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v___y_1420_ = v___x_1434_;
goto v___jp_1419_;
}
}
}
else
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_ptr_addr(v_decl_1398_);
v___x_1440_ = lean_ptr_addr(v_a_1415_);
v___x_1441_ = lean_usize_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_isSharedCheck_1448_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1450_);
v___x_1443_ = v_c_1263_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_c_1263_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_fst_1402_);
lean_ctor_set(v___x_1443_, 0, v_a_1415_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1415_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_fst_1402_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
v___y_1420_ = v___x_1446_;
goto v___jp_1419_;
}
}
}
else
{
lean_dec(v_a_1415_);
lean_dec(v_fst_1402_);
v___y_1420_ = v_c_1263_;
goto v___jp_1419_;
}
}
v___jp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_snd_1403_);
lean_ctor_set(v___x_1412_, 0, v___y_1420_);
v___x_1422_ = v___x_1412_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___y_1420_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_snd_1403_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1422_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_del_object(v___x_1412_);
lean_dec(v_snd_1403_);
lean_dec(v_fst_1402_);
lean_dec_ref_known(v_c_1263_, 2);
v_a_1452_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1414_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1414_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
else
{
lean_dec(v_snd_1403_);
lean_dec(v_fst_1402_);
lean_dec_ref_known(v_c_1263_, 2);
return v___x_1408_;
}
}
else
{
lean_dec_ref_known(v_c_1263_, 2);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
return v___x_1400_;
}
}
case 3:
{
lean_object* v___x_1462_; 
lean_dec_ref(v_info_1262_);
lean_inc_ref(v_c_1263_);
v___x_1462_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1263_, v_x_1261_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1471_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1471_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1471_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_c_1263_);
lean_ctor_set(v___x_1467_, 1, v_a_1463_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1467_);
v___x_1469_ = v___x_1465_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref_known(v_c_1263_, 2);
v_a_1472_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1462_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1462_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
case 4:
{
lean_object* v_cases_1480_; lean_object* v___x_1481_; 
v_cases_1480_ = lean_ctor_get(v_c_1263_, 0);
lean_inc_ref(v_cases_1480_);
lean_inc(v_x_1261_);
lean_inc_ref(v_c_1263_);
v___x_1481_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1263_, v_x_1261_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1534_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1534_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1534_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_unbox(v_a_1482_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_dec_ref(v_cases_1480_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_c_1263_);
lean_ctor_set(v___x_1487_, 1, v_a_1482_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
else
{
lean_object* v_typeName_1491_; lean_object* v_resultType_1492_; lean_object* v_discr_1493_; lean_object* v_alts_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1533_; 
lean_del_object(v___x_1484_);
v_typeName_1491_ = lean_ctor_get(v_cases_1480_, 0);
v_resultType_1492_ = lean_ctor_get(v_cases_1480_, 1);
v_discr_1493_ = lean_ctor_get(v_cases_1480_, 2);
v_alts_1494_ = lean_ctor_get(v_cases_1480_, 3);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_cases_1480_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1496_ = v_cases_1480_;
v_isShared_1497_ = v_isSharedCheck_1533_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_alts_1494_);
lean_inc(v_discr_1493_);
lean_inc(v_resultType_1492_);
lean_inc(v_typeName_1491_);
lean_dec(v_cases_1480_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1533_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1494_);
v___x_1499_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1261_, v_info_1262_, v___x_1498_, v_alts_1494_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1524_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1524_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___y_1505_; size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = lean_ptr_addr(v_alts_1494_);
lean_dec_ref(v_alts_1494_);
v___x_1511_ = lean_ptr_addr(v_a_1500_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1523_);
v___x_1514_ = v_c_1263_;
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_c_1263_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 3, v_a_1500_);
v___x_1517_ = v___x_1496_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_typeName_1491_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_resultType_1492_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_discr_1493_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_a_1500_);
v___x_1517_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1517_);
v___x_1519_ = v___x_1514_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
v___y_1505_ = v___x_1519_;
goto v___jp_1504_;
}
}
}
}
else
{
lean_dec(v_a_1500_);
lean_del_object(v___x_1496_);
lean_dec(v_discr_1493_);
lean_dec_ref(v_resultType_1492_);
lean_dec(v_typeName_1491_);
v___y_1505_ = v_c_1263_;
goto v___jp_1504_;
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___y_1505_);
lean_ctor_set(v___x_1506_, 1, v_a_1482_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1506_);
v___x_1508_ = v___x_1502_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_del_object(v___x_1496_);
lean_dec_ref(v_alts_1494_);
lean_dec(v_discr_1493_);
lean_dec_ref(v_resultType_1492_);
lean_dec(v_typeName_1491_);
lean_dec(v_a_1482_);
lean_dec_ref_known(v_c_1263_, 1);
v_a_1525_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1499_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1499_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_cases_1480_);
lean_dec_ref_known(v_c_1263_, 1);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_a_1535_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1481_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1481_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
case 5:
{
lean_object* v___x_1543_; 
lean_dec_ref(v_info_1262_);
lean_inc_ref(v_c_1263_);
v___x_1543_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1263_, v_x_1261_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_c_1263_);
lean_ctor_set(v___x_1548_, 1, v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref_known(v_c_1263_, 1);
v_a_1553_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1543_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1543_);
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
case 6:
{
lean_object* v___x_1561_; 
lean_dec_ref(v_info_1262_);
lean_inc_ref(v_c_1263_);
v___x_1561_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1263_, v_x_1261_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1570_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_c_1263_);
lean_ctor_set(v___x_1566_, 1, v_a_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref_known(v_c_1263_, 1);
v_a_1571_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1561_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1561_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
case 8:
{
lean_object* v_fvarId_1579_; lean_object* v_i_1580_; lean_object* v_y_1581_; lean_object* v_k_1582_; uint8_t v___x_1583_; lean_object* v_instr_1584_; uint8_t v___x_1585_; uint8_t v___x_1586_; 
v_fvarId_1579_ = lean_ctor_get(v_c_1263_, 0);
v_i_1580_ = lean_ctor_get(v_c_1263_, 1);
v_y_1581_ = lean_ctor_get(v_c_1263_, 2);
v_k_1582_ = lean_ctor_get(v_c_1263_, 3);
v___x_1583_ = 1;
v_instr_1584_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1583_, v_c_1263_);
lean_inc(v_x_1261_);
v___x_1585_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1584_, v_x_1261_);
v___x_1586_ = 1;
if (v___x_1585_ == 0)
{
lean_object* v___x_1587_; 
lean_inc_ref(v_k_1582_);
lean_inc_ref(v_info_1262_);
lean_inc(v_x_1261_);
v___x_1587_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1261_, v_info_1262_, v_k_1582_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1713_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1713_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1713_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___y_1593_; lean_object* v_snd_1599_; uint8_t v___x_1600_; 
v_snd_1599_ = lean_ctor_get(v_a_1588_, 1);
v___x_1600_ = lean_unbox(v_snd_1599_);
if (v___x_1600_ == 0)
{
lean_object* v_fst_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1696_; 
lean_inc(v_snd_1599_);
lean_del_object(v___x_1590_);
v_fst_1601_ = lean_ctor_get(v_a_1588_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_a_1588_, 1);
lean_dec(v_unused_1697_);
v___x_1603_ = v_a_1588_;
v_isShared_1604_ = v_isSharedCheck_1696_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_fst_1601_);
lean_dec(v_a_1588_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1696_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; 
lean_inc(v_x_1261_);
v___x_1605_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1584_, v_x_1261_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1687_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1687_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1687_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___y_1611_; lean_object* v___y_1619_; uint8_t v___x_1623_; 
v___x_1623_ = lean_unbox(v_a_1606_);
lean_dec(v_a_1606_);
switch(v___x_1623_)
{
case 0:
{
size_t v___x_1624_; size_t v___x_1625_; uint8_t v___x_1626_; 
lean_del_object(v___x_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1599_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1624_ = lean_ptr_addr(v_k_1582_);
v___x_1625_ = lean_ptr_addr(v_fst_1601_);
v___x_1626_ = lean_usize_dec_eq(v___x_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_inc(v_y_1581_);
lean_inc(v_i_1580_);
lean_inc(v_fvarId_1579_);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; 
v_unused_1634_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1637_);
v___x_1628_ = v_c_1263_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v_c_1263_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 3, v_fst_1601_);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_fvarId_1579_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_i_1580_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_y_1581_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_fst_1601_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
v___y_1619_ = v___x_1631_;
goto v___jp_1618_;
}
}
}
else
{
lean_dec(v_fst_1601_);
v___y_1619_ = v_c_1263_;
goto v___jp_1618_;
}
}
case 1:
{
lean_object* v___x_1638_; 
lean_del_object(v___x_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1599_);
v___x_1638_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1261_, v_info_1262_, v_fst_1601_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec_ref(v_info_1262_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1664_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1664_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1664_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___y_1644_; size_t v___x_1650_; size_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1650_ = lean_ptr_addr(v_k_1582_);
v___x_1651_ = lean_ptr_addr(v_a_1639_);
v___x_1652_ = lean_usize_dec_eq(v___x_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_inc(v_y_1581_);
lean_inc(v_i_1580_);
lean_inc(v_fvarId_1579_);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1660_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1663_);
v___x_1654_ = v_c_1263_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_dec(v_c_1263_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v_a_1639_);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_fvarId_1579_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_i_1580_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_y_1581_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_a_1639_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v___y_1644_ = v___x_1657_;
goto v___jp_1643_;
}
}
}
else
{
lean_dec(v_a_1639_);
v___y_1644_ = v_c_1263_;
goto v___jp_1643_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1645_ = lean_box(v___x_1586_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___y_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1646_);
v___x_1648_ = v___x_1641_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref_known(v_c_1263_, 4);
v_a_1665_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1638_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1638_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
default: 
{
size_t v___x_1673_; size_t v___x_1674_; uint8_t v___x_1675_; 
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1673_ = lean_ptr_addr(v_k_1582_);
v___x_1674_ = lean_ptr_addr(v_fst_1601_);
v___x_1675_ = lean_usize_dec_eq(v___x_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_inc(v_y_1581_);
lean_inc(v_i_1580_);
lean_inc(v_fvarId_1579_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1683_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1686_);
v___x_1677_ = v_c_1263_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_c_1263_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 3, v_fst_1601_);
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_fvarId_1579_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_i_1580_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_y_1581_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_fst_1601_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v___y_1611_ = v___x_1680_;
goto v___jp_1610_;
}
}
}
else
{
lean_dec(v_fst_1601_);
v___y_1611_ = v_c_1263_;
goto v___jp_1610_;
}
}
}
v___jp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___y_1611_);
v___x_1613_ = v___x_1603_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___y_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_snd_1599_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1613_);
v___x_1615_ = v___x_1608_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
v___jp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_box(v___x_1586_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___y_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1603_);
lean_dec(v_fst_1601_);
lean_dec(v_snd_1599_);
lean_dec_ref_known(v_c_1263_, 4);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_a_1688_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1605_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1605_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
else
{
lean_object* v_fst_1698_; size_t v___x_1699_; size_t v___x_1700_; uint8_t v___x_1701_; 
lean_dec_ref(v_instr_1584_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_fst_1698_ = lean_ctor_get(v_a_1588_, 0);
lean_inc(v_fst_1698_);
lean_dec(v_a_1588_);
v___x_1699_ = lean_ptr_addr(v_k_1582_);
v___x_1700_ = lean_ptr_addr(v_fst_1698_);
v___x_1701_ = lean_usize_dec_eq(v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_inc(v_y_1581_);
lean_inc(v_i_1580_);
lean_inc(v_fvarId_1579_);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; 
v_unused_1709_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1712_);
v___x_1703_ = v_c_1263_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_c_1263_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 3, v_fst_1698_);
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_fvarId_1579_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_i_1580_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_y_1581_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_fst_1698_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
v___y_1593_ = v___x_1706_;
goto v___jp_1592_;
}
}
}
else
{
lean_dec(v_fst_1698_);
v___y_1593_ = v_c_1263_;
goto v___jp_1592_;
}
}
v___jp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = lean_box(v___x_1586_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___y_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1595_);
v___x_1597_ = v___x_1590_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1584_);
lean_dec_ref_known(v_c_1263_, 4);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
return v___x_1587_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref(v_instr_1584_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1714_ = lean_box(v___x_1586_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_c_1263_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
case 9:
{
lean_object* v_fvarId_1717_; lean_object* v_i_1718_; lean_object* v_offset_1719_; lean_object* v_y_1720_; lean_object* v_ty_1721_; lean_object* v_k_1722_; uint8_t v___x_1723_; lean_object* v_instr_1724_; uint8_t v___x_1725_; uint8_t v___x_1726_; 
v_fvarId_1717_ = lean_ctor_get(v_c_1263_, 0);
v_i_1718_ = lean_ctor_get(v_c_1263_, 1);
v_offset_1719_ = lean_ctor_get(v_c_1263_, 2);
v_y_1720_ = lean_ctor_get(v_c_1263_, 3);
v_ty_1721_ = lean_ctor_get(v_c_1263_, 4);
v_k_1722_ = lean_ctor_get(v_c_1263_, 5);
v___x_1723_ = 1;
v_instr_1724_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1723_, v_c_1263_);
lean_inc(v_x_1261_);
v___x_1725_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1724_, v_x_1261_);
v___x_1726_ = 1;
if (v___x_1725_ == 0)
{
lean_object* v___x_1727_; 
lean_inc_ref(v_k_1722_);
lean_inc_ref(v_info_1262_);
lean_inc(v_x_1261_);
v___x_1727_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1261_, v_info_1262_, v_k_1722_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1861_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1861_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1861_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___y_1733_; lean_object* v_snd_1739_; uint8_t v___x_1740_; 
v_snd_1739_ = lean_ctor_get(v_a_1728_, 1);
v___x_1740_ = lean_unbox(v_snd_1739_);
if (v___x_1740_ == 0)
{
lean_object* v_fst_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1842_; 
lean_inc(v_snd_1739_);
lean_del_object(v___x_1730_);
v_fst_1741_ = lean_ctor_get(v_a_1728_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_a_1728_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_a_1728_, 1);
lean_dec(v_unused_1843_);
v___x_1743_ = v_a_1728_;
v_isShared_1744_ = v_isSharedCheck_1842_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_fst_1741_);
lean_dec(v_a_1728_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1842_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; 
lean_inc(v_x_1261_);
v___x_1745_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1724_, v_x_1261_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1833_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1833_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1833_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___y_1751_; lean_object* v___y_1759_; uint8_t v___x_1763_; 
v___x_1763_ = lean_unbox(v_a_1746_);
lean_dec(v_a_1746_);
switch(v___x_1763_)
{
case 0:
{
size_t v___x_1764_; size_t v___x_1765_; uint8_t v___x_1766_; 
lean_del_object(v___x_1748_);
lean_del_object(v___x_1743_);
lean_dec(v_snd_1739_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1764_ = lean_ptr_addr(v_k_1722_);
v___x_1765_ = lean_ptr_addr(v_fst_1741_);
v___x_1766_ = lean_usize_dec_eq(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_inc_ref(v_ty_1721_);
lean_inc(v_y_1720_);
lean_inc(v_offset_1719_);
lean_inc(v_i_1718_);
lean_inc(v_fvarId_1717_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; 
v_unused_1774_ = lean_ctor_get(v_c_1263_, 5);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_c_1263_, 4);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1779_);
v___x_1768_ = v_c_1263_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v_c_1263_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 5, v_fst_1741_);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_fvarId_1717_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_i_1718_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_offset_1719_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_y_1720_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v_ty_1721_);
lean_ctor_set(v_reuseFailAlloc_1772_, 5, v_fst_1741_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v___y_1759_ = v___x_1771_;
goto v___jp_1758_;
}
}
}
else
{
lean_dec(v_fst_1741_);
v___y_1759_ = v_c_1263_;
goto v___jp_1758_;
}
}
case 1:
{
lean_object* v___x_1780_; 
lean_del_object(v___x_1748_);
lean_del_object(v___x_1743_);
lean_dec(v_snd_1739_);
v___x_1780_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1261_, v_info_1262_, v_fst_1741_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec_ref(v_info_1262_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1808_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1808_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1808_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___y_1786_; size_t v___x_1792_; size_t v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_ptr_addr(v_k_1722_);
v___x_1793_ = lean_ptr_addr(v_a_1781_);
v___x_1794_ = lean_usize_dec_eq(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_inc_ref(v_ty_1721_);
lean_inc(v_y_1720_);
lean_inc(v_offset_1719_);
lean_inc(v_i_1718_);
lean_inc(v_fvarId_1717_);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; 
v_unused_1802_ = lean_ctor_get(v_c_1263_, 5);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_c_1263_, 4);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1807_);
v___x_1796_ = v_c_1263_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_dec(v_c_1263_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 5, v_a_1781_);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_fvarId_1717_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_i_1718_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_offset_1719_);
lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_y_1720_);
lean_ctor_set(v_reuseFailAlloc_1800_, 4, v_ty_1721_);
lean_ctor_set(v_reuseFailAlloc_1800_, 5, v_a_1781_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
v___y_1786_ = v___x_1799_;
goto v___jp_1785_;
}
}
}
else
{
lean_dec(v_a_1781_);
v___y_1786_ = v_c_1263_;
goto v___jp_1785_;
}
v___jp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1787_ = lean_box(v___x_1726_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___y_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1788_);
v___x_1790_ = v___x_1783_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref_known(v_c_1263_, 6);
v_a_1809_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1780_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1780_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
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
default: 
{
size_t v___x_1817_; size_t v___x_1818_; uint8_t v___x_1819_; 
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1817_ = lean_ptr_addr(v_k_1722_);
v___x_1818_ = lean_ptr_addr(v_fst_1741_);
v___x_1819_ = lean_usize_dec_eq(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_inc_ref(v_ty_1721_);
lean_inc(v_y_1720_);
lean_inc(v_offset_1719_);
lean_inc(v_i_1718_);
lean_inc(v_fvarId_1717_);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; 
v_unused_1827_ = lean_ctor_get(v_c_1263_, 5);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_c_1263_, 4);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1829_);
v_unused_1830_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1832_);
v___x_1821_ = v_c_1263_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v_c_1263_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 5, v_fst_1741_);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_fvarId_1717_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_i_1718_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_offset_1719_);
lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_y_1720_);
lean_ctor_set(v_reuseFailAlloc_1825_, 4, v_ty_1721_);
lean_ctor_set(v_reuseFailAlloc_1825_, 5, v_fst_1741_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
v___y_1751_ = v___x_1824_;
goto v___jp_1750_;
}
}
}
else
{
lean_dec(v_fst_1741_);
v___y_1751_ = v_c_1263_;
goto v___jp_1750_;
}
}
}
v___jp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___y_1751_);
v___x_1753_ = v___x_1743_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___y_1751_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_snd_1739_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1753_);
v___x_1755_ = v___x_1748_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
v___jp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_box(v___x_1726_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_del_object(v___x_1743_);
lean_dec(v_fst_1741_);
lean_dec(v_snd_1739_);
lean_dec_ref_known(v_c_1263_, 6);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_a_1834_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1745_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1745_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
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
}
else
{
lean_object* v_fst_1844_; size_t v___x_1845_; size_t v___x_1846_; uint8_t v___x_1847_; 
lean_dec_ref(v_instr_1724_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v_fst_1844_ = lean_ctor_get(v_a_1728_, 0);
lean_inc(v_fst_1844_);
lean_dec(v_a_1728_);
v___x_1845_ = lean_ptr_addr(v_k_1722_);
v___x_1846_ = lean_ptr_addr(v_fst_1844_);
v___x_1847_ = lean_usize_dec_eq(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_inc_ref(v_ty_1721_);
lean_inc(v_y_1720_);
lean_inc(v_offset_1719_);
lean_inc(v_i_1718_);
lean_inc(v_fvarId_1717_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_c_1263_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1855_ = lean_ctor_get(v_c_1263_, 5);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_c_1263_, 4);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_c_1263_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_c_1263_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_c_1263_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_c_1263_, 0);
lean_dec(v_unused_1860_);
v___x_1849_ = v_c_1263_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v_c_1263_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 5, v_fst_1844_);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_fvarId_1717_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_i_1718_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_offset_1719_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_y_1720_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_ty_1721_);
lean_ctor_set(v_reuseFailAlloc_1853_, 5, v_fst_1844_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v___y_1733_ = v___x_1852_;
goto v___jp_1732_;
}
}
}
else
{
lean_dec(v_fst_1844_);
v___y_1733_ = v_c_1263_;
goto v___jp_1732_;
}
}
v___jp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1734_ = lean_box(v___x_1726_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___y_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1735_);
v___x_1737_ = v___x_1730_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1724_);
lean_dec_ref_known(v_c_1263_, 6);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
return v___x_1727_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_instr_1724_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1862_ = lean_box(v___x_1726_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_c_1263_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
default: 
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec_ref(v_c_1263_);
lean_dec_ref(v_info_1262_);
lean_dec(v_x_1261_);
v___x_1865_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
v___x_1866_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_1865_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(lean_object* v_x_1867_, lean_object* v_info_1868_, lean_object* v_c_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; 
lean_inc_ref(v_info_1868_);
lean_inc(v_x_1867_);
v___x_1876_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1867_, v_info_1868_, v_c_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1889_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1889_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1889_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_snd_1881_; uint8_t v___x_1882_; 
v_snd_1881_ = lean_ctor_get(v_a_1877_, 1);
v___x_1882_ = lean_unbox(v_snd_1881_);
if (v___x_1882_ == 0)
{
lean_object* v_fst_1883_; lean_object* v___x_1884_; 
lean_del_object(v___x_1879_);
v_fst_1883_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_fst_1883_);
lean_dec(v_a_1877_);
v___x_1884_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1867_, v_info_1868_, v_fst_1883_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
lean_dec_ref(v_info_1868_);
return v___x_1884_;
}
else
{
lean_object* v_fst_1885_; lean_object* v___x_1887_; 
lean_dec_ref(v_info_1868_);
lean_dec(v_x_1867_);
v_fst_1885_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_fst_1885_);
lean_dec(v_a_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_fst_1885_);
v___x_1887_ = v___x_1879_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_fst_1885_);
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
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_info_1868_);
lean_dec(v_x_1867_);
v_a_1890_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1876_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1876_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1___boxed(lean_object* v_x_1898_, lean_object* v_info_1899_, lean_object* v_i_1900_, lean_object* v_as_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1898_, v_info_1899_, v_i_1900_, v_as_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___boxed(lean_object* v_x_1909_, lean_object* v_info_1910_, lean_object* v_c_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1909_, v_info_1910_, v_c_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec_ref(v_a_1912_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(uint8_t v_pu_1919_, lean_object* v_alt_1920_, lean_object* v_f_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1920_, v_f_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___boxed(lean_object* v_pu_1929_, lean_object* v_alt_1930_, lean_object* v_f_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
uint8_t v_pu_boxed_1938_; lean_object* v_res_1939_; 
v_pu_boxed_1938_ = lean_unbox(v_pu_1929_);
v_res_1939_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0(v_pu_boxed_1938_, v_alt_1930_, v_f_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(lean_object* v_msg_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_toApplicative_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1983_; 
v___x_1947_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_1948_ = l_StateRefT_x27_instMonad___redArg(v___x_1947_);
v_toApplicative_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v___x_1948_, 1);
lean_dec(v_unused_1984_);
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1983_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_toApplicative_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1983_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_toFunctor_1953_; lean_object* v_toSeq_1954_; lean_object* v_toSeqLeft_1955_; lean_object* v_toSeqRight_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1981_; 
v_toFunctor_1953_ = lean_ctor_get(v_toApplicative_1949_, 0);
v_toSeq_1954_ = lean_ctor_get(v_toApplicative_1949_, 2);
v_toSeqLeft_1955_ = lean_ctor_get(v_toApplicative_1949_, 3);
v_toSeqRight_1956_ = lean_ctor_get(v_toApplicative_1949_, 4);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_toApplicative_1949_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_toApplicative_1949_, 1);
lean_dec(v_unused_1982_);
v___x_1958_ = v_toApplicative_1949_;
v_isShared_1959_ = v_isSharedCheck_1981_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_toSeqRight_1956_);
lean_inc(v_toSeqLeft_1955_);
lean_inc(v_toSeq_1954_);
lean_inc(v_toFunctor_1953_);
lean_dec(v_toApplicative_1949_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1981_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___f_1960_; lean_object* v___f_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___f_1966_; lean_object* v___f_1967_; lean_object* v___x_1969_; 
v___f_1960_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_1961_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_1953_);
v___f_1962_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1962_, 0, v_toFunctor_1953_);
v___f_1963_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1963_, 0, v_toFunctor_1953_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___f_1962_);
lean_ctor_set(v___x_1964_, 1, v___f_1963_);
v___f_1965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1965_, 0, v_toSeqRight_1956_);
v___f_1966_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1966_, 0, v_toSeqLeft_1955_);
v___f_1967_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1967_, 0, v_toSeq_1954_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v___f_1965_);
lean_ctor_set(v___x_1958_, 3, v___f_1966_);
lean_ctor_set(v___x_1958_, 2, v___f_1967_);
lean_ctor_set(v___x_1958_, 1, v___f_1960_);
lean_ctor_set(v___x_1958_, 0, v___x_1964_);
v___x_1969_ = v___x_1958_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___f_1960_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v___f_1967_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v___f_1966_);
lean_ctor_set(v_reuseFailAlloc_1980_, 4, v___f_1965_);
v___x_1969_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v___f_1961_);
lean_ctor_set(v___x_1951_, 0, v___x_1969_);
v___x_1971_ = v___x_1951_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___f_1961_);
v___x_1971_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_5524__overap_1977_; lean_object* v___x_1978_; 
v___x_1972_ = l_StateRefT_x27_instMonad___redArg(v___x_1971_);
v___x_1973_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_1974_ = l_instInhabitedOfMonad___redArg(v___x_1972_, v___x_1973_);
v___f_1975_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1975_, 0, v___x_1974_);
v___f_1976_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1976_, 0, v___f_1975_);
v___x_5524__overap_1977_ = lean_panic_fn_borrowed(v___f_1976_, v_msg_1940_);
lean_dec_ref(v___f_1976_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1944_);
lean_inc(v___y_1943_);
lean_inc_ref(v___y_1942_);
lean_inc_ref(v___y_1941_);
v___x_1978_ = lean_apply_6(v___x_5524__overap_1977_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, lean_box(0));
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4___boxed(lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v_msg_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v___y_1986_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(lean_object* v_a_1993_, lean_object* v_fallback_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_inc(v_fallback_1994_);
return v_fallback_1994_;
}
else
{
lean_object* v_key_1996_; lean_object* v_value_1997_; lean_object* v_tail_1998_; uint8_t v___x_1999_; 
v_key_1996_ = lean_ctor_get(v_x_1995_, 0);
v_value_1997_ = lean_ctor_get(v_x_1995_, 1);
v_tail_1998_ = lean_ctor_get(v_x_1995_, 2);
v___x_1999_ = l_Lean_instBEqFVarId_beq(v_key_1996_, v_a_1993_);
if (v___x_1999_ == 0)
{
v_x_1995_ = v_tail_1998_;
goto _start;
}
else
{
lean_inc(v_value_1997_);
return v_value_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg___boxed(lean_object* v_a_2001_, lean_object* v_fallback_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2001_, v_fallback_2002_, v_x_2003_);
lean_dec(v_x_2003_);
lean_dec(v_fallback_2002_);
lean_dec(v_a_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(lean_object* v_m_2005_, lean_object* v_a_2006_, lean_object* v_fallback_2007_){
_start:
{
lean_object* v_buckets_2008_; lean_object* v___x_2009_; uint64_t v___x_2010_; uint64_t v___x_2011_; uint64_t v___x_2012_; uint64_t v_fold_2013_; uint64_t v___x_2014_; uint64_t v___x_2015_; uint64_t v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_buckets_2008_ = lean_ctor_get(v_m_2005_, 1);
v___x_2009_ = lean_array_get_size(v_buckets_2008_);
v___x_2010_ = l_Lean_instHashableFVarId_hash(v_a_2006_);
v___x_2011_ = 32ULL;
v___x_2012_ = lean_uint64_shift_right(v___x_2010_, v___x_2011_);
v_fold_2013_ = lean_uint64_xor(v___x_2010_, v___x_2012_);
v___x_2014_ = 16ULL;
v___x_2015_ = lean_uint64_shift_right(v_fold_2013_, v___x_2014_);
v___x_2016_ = lean_uint64_xor(v_fold_2013_, v___x_2015_);
v___x_2017_ = lean_uint64_to_usize(v___x_2016_);
v___x_2018_ = lean_usize_of_nat(v___x_2009_);
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_sub(v___x_2018_, v___x_2019_);
v___x_2021_ = lean_usize_land(v___x_2017_, v___x_2020_);
v___x_2022_ = lean_array_uget_borrowed(v_buckets_2008_, v___x_2021_);
v___x_2023_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2006_, v_fallback_2007_, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg___boxed(lean_object* v_m_2024_, lean_object* v_a_2025_, lean_object* v_fallback_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2024_, v_a_2025_, v_fallback_2026_);
lean_dec(v_fallback_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_m_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
lean_object* v_ks_2032_; lean_object* v_vs_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2057_; 
v_ks_2032_ = lean_ctor_get(v_x_2028_, 0);
v_vs_2033_ = lean_ctor_get(v_x_2028_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2035_ = v_x_2028_;
v_isShared_2036_ = v_isSharedCheck_2057_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_vs_2033_);
lean_inc(v_ks_2032_);
lean_dec(v_x_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2057_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_array_get_size(v_ks_2032_);
v___x_2038_ = lean_nat_dec_lt(v_x_2029_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec(v_x_2029_);
v___x_2039_ = lean_array_push(v_ks_2032_, v_x_2030_);
v___x_2040_ = lean_array_push(v_vs_2033_, v_x_2031_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v___x_2040_);
lean_ctor_set(v___x_2035_, 0, v___x_2039_);
v___x_2042_ = v___x_2035_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
else
{
lean_object* v_k_x27_2044_; uint8_t v___x_2045_; 
v_k_x27_2044_ = lean_array_fget_borrowed(v_ks_2032_, v_x_2029_);
v___x_2045_ = l_Lean_instBEqFVarId_beq(v_x_2030_, v_k_x27_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2047_; 
if (v_isShared_2036_ == 0)
{
v___x_2047_ = v___x_2035_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_ks_2032_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_vs_2033_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(1u);
v___x_2049_ = lean_nat_add(v_x_2029_, v___x_2048_);
lean_dec(v_x_2029_);
v_x_2028_ = v___x_2047_;
v_x_2029_ = v___x_2049_;
goto _start;
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2052_ = lean_array_fset(v_ks_2032_, v_x_2029_, v_x_2030_);
v___x_2053_ = lean_array_fset(v_vs_2033_, v_x_2029_, v_x_2031_);
lean_dec(v_x_2029_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v___x_2053_);
lean_ctor_set(v___x_2035_, 0, v___x_2052_);
v___x_2055_ = v___x_2035_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(lean_object* v_n_2058_, lean_object* v_k_2059_, lean_object* v_v_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_n_2058_, v___x_2061_, v_k_2059_, v_v_2060_);
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object* v_x_2064_, size_t v_x_2065_, size_t v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
if (lean_obj_tag(v_x_2064_) == 0)
{
lean_object* v_es_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v_j_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_es_2069_ = lean_ctor_get(v_x_2064_, 0);
v___x_2070_ = ((size_t)31ULL);
v___x_2071_ = lean_usize_land(v_x_2065_, v___x_2070_);
v_j_2072_ = lean_usize_to_nat(v___x_2071_);
v___x_2073_ = lean_array_get_size(v_es_2069_);
v___x_2074_ = lean_nat_dec_lt(v_j_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_j_2072_);
lean_dec(v_x_2068_);
lean_dec(v_x_2067_);
return v_x_2064_;
}
else
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2113_; 
lean_inc_ref(v_es_2069_);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v_x_2064_, 0);
lean_dec(v_unused_2114_);
v___x_2076_ = v_x_2064_;
v_isShared_2077_ = v_isSharedCheck_2113_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_x_2064_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2113_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_v_2078_; lean_object* v___x_2079_; lean_object* v_xs_x27_2080_; lean_object* v___y_2082_; 
v_v_2078_ = lean_array_fget(v_es_2069_, v_j_2072_);
v___x_2079_ = lean_box(0);
v_xs_x27_2080_ = lean_array_fset(v_es_2069_, v_j_2072_, v___x_2079_);
switch(lean_obj_tag(v_v_2078_))
{
case 0:
{
lean_object* v_key_2087_; lean_object* v_val_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2098_; 
v_key_2087_ = lean_ctor_get(v_v_2078_, 0);
v_val_2088_ = lean_ctor_get(v_v_2078_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_v_2078_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2090_ = v_v_2078_;
v_isShared_2091_ = v_isSharedCheck_2098_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_val_2088_);
lean_inc(v_key_2087_);
lean_dec(v_v_2078_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2098_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
uint8_t v___x_2092_; 
v___x_2092_ = l_Lean_instBEqFVarId_beq(v_x_2067_, v_key_2087_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_del_object(v___x_2090_);
v___x_2093_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2087_, v_val_2088_, v_x_2067_, v_x_2068_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
v___y_2082_ = v___x_2094_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2096_; 
lean_dec(v_val_2088_);
lean_dec(v_key_2087_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v_x_2068_);
lean_ctor_set(v___x_2090_, 0, v_x_2067_);
v___x_2096_ = v___x_2090_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_x_2067_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_x_2068_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
v___y_2082_ = v___x_2096_;
goto v___jp_2081_;
}
}
}
}
case 1:
{
lean_object* v_node_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2111_; 
v_node_2099_ = lean_ctor_get(v_v_2078_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_v_2078_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2101_ = v_v_2078_;
v_isShared_2102_ = v_isSharedCheck_2111_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_node_2099_);
lean_dec(v_v_2078_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2111_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
size_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2103_ = ((size_t)5ULL);
v___x_2104_ = lean_usize_shift_right(v_x_2065_, v___x_2103_);
v___x_2105_ = ((size_t)1ULL);
v___x_2106_ = lean_usize_add(v_x_2066_, v___x_2105_);
v___x_2107_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_2099_, v___x_2104_, v___x_2106_, v_x_2067_, v_x_2068_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2107_);
v___x_2109_ = v___x_2101_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
v___y_2082_ = v___x_2109_;
goto v___jp_2081_;
}
}
}
default: 
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_x_2067_);
lean_ctor_set(v___x_2112_, 1, v_x_2068_);
v___y_2082_ = v___x_2112_;
goto v___jp_2081_;
}
}
v___jp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_array_fset(v_xs_x27_2080_, v_j_2072_, v___y_2082_);
lean_dec(v_j_2072_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2083_);
v___x_2085_ = v___x_2076_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
else
{
lean_object* v_ks_2115_; lean_object* v_vs_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2134_; 
v_ks_2115_ = lean_ctor_get(v_x_2064_, 0);
v_vs_2116_ = lean_ctor_get(v_x_2064_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2118_ = v_x_2064_;
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_vs_2116_);
lean_inc(v_ks_2115_);
lean_dec(v_x_2064_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_ks_2115_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_vs_2116_);
v___x_2121_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v_newNode_2122_; size_t v___x_2123_; uint8_t v___x_2124_; 
v_newNode_2122_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_2121_, v_x_2067_, v_x_2068_);
v___x_2123_ = ((size_t)7ULL);
v___x_2124_ = lean_usize_dec_le(v___x_2123_, v_x_2066_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2122_);
v___x_2126_ = lean_unsigned_to_nat(4u);
v___x_2127_ = lean_nat_dec_lt(v___x_2125_, v___x_2126_);
lean_dec(v___x_2125_);
if (v___x_2127_ == 0)
{
lean_object* v_ks_2128_; lean_object* v_vs_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_ks_2128_ = lean_ctor_get(v_newNode_2122_, 0);
lean_inc_ref(v_ks_2128_);
v_vs_2129_ = lean_ctor_get(v_newNode_2122_, 1);
lean_inc_ref(v_vs_2129_);
lean_dec_ref(v_newNode_2122_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_2066_, v_ks_2128_, v_vs_2129_, v___x_2130_, v___x_2131_);
lean_dec_ref(v_vs_2129_);
lean_dec_ref(v_ks_2128_);
return v___x_2132_;
}
else
{
return v_newNode_2122_;
}
}
else
{
return v_newNode_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t v_depth_2135_, lean_object* v_keys_2136_, lean_object* v_vals_2137_, lean_object* v_i_2138_, lean_object* v_entries_2139_){
_start:
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = lean_array_get_size(v_keys_2136_);
v___x_2141_ = lean_nat_dec_lt(v_i_2138_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_dec(v_i_2138_);
return v_entries_2139_;
}
else
{
lean_object* v_k_2142_; lean_object* v_v_2143_; uint64_t v___x_2144_; size_t v_h_2145_; size_t v___x_2146_; lean_object* v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; size_t v___x_2150_; size_t v_h_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_k_2142_ = lean_array_fget_borrowed(v_keys_2136_, v_i_2138_);
v_v_2143_ = lean_array_fget_borrowed(v_vals_2137_, v_i_2138_);
v___x_2144_ = l_Lean_instHashableFVarId_hash(v_k_2142_);
v_h_2145_ = lean_uint64_to_usize(v___x_2144_);
v___x_2146_ = ((size_t)5ULL);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_sub(v_depth_2135_, v___x_2148_);
v___x_2150_ = lean_usize_mul(v___x_2146_, v___x_2149_);
v_h_2151_ = lean_usize_shift_right(v_h_2145_, v___x_2150_);
v___x_2152_ = lean_nat_add(v_i_2138_, v___x_2147_);
lean_dec(v_i_2138_);
lean_inc(v_v_2143_);
lean_inc(v_k_2142_);
v___x_2153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2139_, v_h_2151_, v_depth_2135_, v_k_2142_, v_v_2143_);
v_i_2138_ = v___x_2152_;
v_entries_2139_ = v___x_2153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_2155_, lean_object* v_keys_2156_, lean_object* v_vals_2157_, lean_object* v_i_2158_, lean_object* v_entries_2159_){
_start:
{
size_t v_depth_boxed_2160_; lean_object* v_res_2161_; 
v_depth_boxed_2160_ = lean_unbox_usize(v_depth_2155_);
lean_dec(v_depth_2155_);
v_res_2161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2160_, v_keys_2156_, v_vals_2157_, v_i_2158_, v_entries_2159_);
lean_dec_ref(v_vals_2157_);
lean_dec_ref(v_keys_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
size_t v_x_6168__boxed_2167_; size_t v_x_6169__boxed_2168_; lean_object* v_res_2169_; 
v_x_6168__boxed_2167_ = lean_unbox_usize(v_x_2163_);
lean_dec(v_x_2163_);
v_x_6169__boxed_2168_ = lean_unbox_usize(v_x_2164_);
lean_dec(v_x_2164_);
v_res_2169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2162_, v_x_6168__boxed_2167_, v_x_6169__boxed_2168_, v_x_2165_, v_x_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_){
_start:
{
uint64_t v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = l_Lean_instHashableFVarId_hash(v_x_2171_);
v___x_2174_ = lean_uint64_to_usize(v___x_2173_);
v___x_2175_ = ((size_t)1ULL);
v___x_2176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2170_, v___x_2174_, v___x_2175_, v_x_2171_, v_x_2172_);
return v___x_2176_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2177_, lean_object* v_i_2178_, lean_object* v_k_2179_){
_start:
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_array_get_size(v_keys_2177_);
v___x_2181_ = lean_nat_dec_lt(v_i_2178_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec(v_i_2178_);
return v___x_2181_;
}
else
{
lean_object* v_k_x27_2182_; uint8_t v___x_2183_; 
v_k_x27_2182_ = lean_array_fget_borrowed(v_keys_2177_, v_i_2178_);
v___x_2183_ = l_Lean_instBEqFVarId_beq(v_k_2179_, v_k_x27_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_add(v_i_2178_, v___x_2184_);
lean_dec(v_i_2178_);
v_i_2178_ = v___x_2185_;
goto _start;
}
else
{
lean_dec(v_i_2178_);
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2187_, lean_object* v_i_2188_, lean_object* v_k_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2187_, v_i_2188_, v_k_2189_);
lean_dec(v_k_2189_);
lean_dec_ref(v_keys_2187_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2192_, size_t v_x_2193_, lean_object* v_x_2194_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_object* v_es_2195_; lean_object* v___x_2196_; size_t v___x_2197_; size_t v___x_2198_; lean_object* v_j_2199_; lean_object* v___x_2200_; 
v_es_2195_ = lean_ctor_get(v_x_2192_, 0);
v___x_2196_ = lean_box(2);
v___x_2197_ = ((size_t)31ULL);
v___x_2198_ = lean_usize_land(v_x_2193_, v___x_2197_);
v_j_2199_ = lean_usize_to_nat(v___x_2198_);
v___x_2200_ = lean_array_get_borrowed(v___x_2196_, v_es_2195_, v_j_2199_);
lean_dec(v_j_2199_);
switch(lean_obj_tag(v___x_2200_))
{
case 0:
{
lean_object* v_key_2201_; uint8_t v___x_2202_; 
v_key_2201_ = lean_ctor_get(v___x_2200_, 0);
v___x_2202_ = l_Lean_instBEqFVarId_beq(v_x_2194_, v_key_2201_);
return v___x_2202_;
}
case 1:
{
lean_object* v_node_2203_; size_t v___x_2204_; size_t v___x_2205_; 
v_node_2203_ = lean_ctor_get(v___x_2200_, 0);
v___x_2204_ = ((size_t)5ULL);
v___x_2205_ = lean_usize_shift_right(v_x_2193_, v___x_2204_);
v_x_2192_ = v_node_2203_;
v_x_2193_ = v___x_2205_;
goto _start;
}
default: 
{
uint8_t v___x_2207_; 
v___x_2207_ = 0;
return v___x_2207_;
}
}
}
else
{
lean_object* v_ks_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_ks_2208_ = lean_ctor_get(v_x_2192_, 0);
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2208_, v___x_2209_, v_x_2194_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_){
_start:
{
size_t v_x_6346__boxed_2214_; uint8_t v_res_2215_; lean_object* v_r_2216_; 
v_x_6346__boxed_2214_ = lean_unbox_usize(v_x_2212_);
lean_dec(v_x_2212_);
v_res_2215_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2211_, v_x_6346__boxed_2214_, v_x_2213_);
lean_dec(v_x_2213_);
lean_dec_ref(v_x_2211_);
v_r_2216_ = lean_box(v_res_2215_);
return v_r_2216_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
uint64_t v___x_2219_; size_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2219_ = l_Lean_instHashableFVarId_hash(v_x_2218_);
v___x_2220_ = lean_uint64_to_usize(v___x_2219_);
v___x_2221_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2217_, v___x_2220_, v_x_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2222_, lean_object* v_x_2223_){
_start:
{
uint8_t v_res_2224_; lean_object* v_r_2225_; 
v_res_2224_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2222_, v_x_2223_);
lean_dec(v_x_2223_);
lean_dec_ref(v_x_2222_);
v_r_2225_ = lean_box(v_res_2224_);
return v_r_2225_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2228_ = lean_unsigned_to_nat(59u);
v___x_2229_ = lean_unsigned_to_nat(281u);
v___x_2230_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2231_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2232_ = l_mkPanicMessageWithDecl(v___x_2231_, v___x_2230_, v___x_2229_, v___x_2228_, v___x_2227_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
switch(lean_obj_tag(v_c_2233_))
{
case 0:
{
lean_object* v_decl_2240_; lean_object* v_k_2241_; lean_object* v___x_2242_; 
v_decl_2240_ = lean_ctor_get(v_c_2233_, 0);
v_k_2241_ = lean_ctor_get(v_c_2233_, 1);
lean_inc_ref(v_k_2241_);
v___x_2242_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2241_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2265_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2265_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2265_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
size_t v___x_2247_; size_t v___x_2248_; uint8_t v___x_2249_; 
v___x_2247_ = lean_ptr_addr(v_k_2241_);
v___x_2248_ = lean_ptr_addr(v_a_2243_);
v___x_2249_ = lean_usize_dec_eq(v___x_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2259_; 
lean_inc_ref(v_decl_2240_);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_c_2233_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; 
v_unused_2260_ = lean_ctor_get(v_c_2233_, 1);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_c_2233_, 0);
lean_dec(v_unused_2261_);
v___x_2251_ = v_c_2233_;
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
else
{
lean_dec(v_c_2233_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 1, v_a_2243_);
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_decl_2240_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_a_2243_);
v___x_2254_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2254_);
v___x_2256_ = v___x_2245_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v___x_2263_; 
lean_dec(v_a_2243_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v_c_2233_);
v___x_2263_ = v___x_2245_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_c_2233_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2233_, 2);
return v___x_2242_;
}
}
case 2:
{
lean_object* v_decl_2266_; lean_object* v_k_2267_; lean_object* v_params_2268_; lean_object* v_type_2269_; lean_object* v_value_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; 
v_decl_2266_ = lean_ctor_get(v_c_2233_, 0);
v_k_2267_ = lean_ctor_get(v_c_2233_, 1);
v_params_2268_ = lean_ctor_get(v_decl_2266_, 2);
v_type_2269_ = lean_ctor_get(v_decl_2266_, 3);
v_value_2270_ = lean_ctor_get(v_decl_2266_, 4);
v___x_2271_ = 1;
lean_inc_ref(v_value_2270_);
v___x_2272_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2270_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
lean_inc_ref(v_params_2268_);
lean_inc_ref(v_type_2269_);
lean_inc_ref(v_decl_2266_);
v___x_2274_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2271_, v_decl_2266_, v_type_2269_, v_params_2268_, v_a_2273_, v_a_2236_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
lean_inc_ref(v_k_2267_);
v___x_2276_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2267_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2314_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2314_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2314_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
size_t v___x_2281_; size_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2281_ = lean_ptr_addr(v_k_2267_);
v___x_2282_ = lean_ptr_addr(v_a_2277_);
v___x_2283_ = lean_usize_dec_eq(v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2293_; 
v_isSharedCheck_2293_ = !lean_is_exclusive(v_c_2233_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; 
v_unused_2294_ = lean_ctor_get(v_c_2233_, 1);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_c_2233_, 0);
lean_dec(v_unused_2295_);
v___x_2285_ = v_c_2233_;
v_isShared_2286_ = v_isSharedCheck_2293_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_c_2233_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2293_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v_a_2277_);
lean_ctor_set(v___x_2285_, 0, v_a_2275_);
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2275_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_a_2277_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2288_);
v___x_2290_ = v___x_2279_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
size_t v___x_2296_; size_t v___x_2297_; uint8_t v___x_2298_; 
v___x_2296_ = lean_ptr_addr(v_decl_2266_);
v___x_2297_ = lean_ptr_addr(v_a_2275_);
v___x_2298_ = lean_usize_dec_eq(v___x_2296_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v_c_2233_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; lean_object* v_unused_2310_; 
v_unused_2309_ = lean_ctor_get(v_c_2233_, 1);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_c_2233_, 0);
lean_dec(v_unused_2310_);
v___x_2300_ = v_c_2233_;
v_isShared_2301_ = v_isSharedCheck_2308_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v_c_2233_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2308_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v_a_2277_);
lean_ctor_set(v___x_2300_, 0, v_a_2275_);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2275_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_a_2277_);
v___x_2303_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2305_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2303_);
v___x_2305_ = v___x_2279_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v___x_2312_; 
lean_dec(v_a_2277_);
lean_dec(v_a_2275_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_c_2233_);
v___x_2312_ = v___x_2279_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_c_2233_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
else
{
lean_dec(v_a_2275_);
lean_dec_ref_known(v_c_2233_, 2);
return v___x_2276_;
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref_known(v_c_2233_, 2);
v_a_2315_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2274_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2274_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2233_, 2);
return v___x_2272_;
}
}
case 3:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_c_2233_);
return v___x_2323_;
}
case 4:
{
lean_object* v_cases_2324_; lean_object* v_typeName_2325_; lean_object* v_resultType_2326_; lean_object* v_discr_2327_; lean_object* v_alts_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2381_; 
v_cases_2324_ = lean_ctor_get(v_c_2233_, 0);
lean_inc_ref(v_cases_2324_);
v_typeName_2325_ = lean_ctor_get(v_cases_2324_, 0);
v_resultType_2326_ = lean_ctor_get(v_cases_2324_, 1);
v_discr_2327_ = lean_ctor_get(v_cases_2324_, 2);
v_alts_2328_ = lean_ctor_get(v_cases_2324_, 3);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_cases_2324_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2330_ = v_cases_2324_;
v_isShared_2331_ = v_isSharedCheck_2381_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_alts_2328_);
lean_inc(v_discr_2327_);
lean_inc(v_resultType_2326_);
lean_inc(v_typeName_2325_);
lean_dec(v_cases_2324_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2381_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_alreadyFound_2332_; uint8_t v_relaxedReuse_2333_; lean_object* v_ownedness_2334_; uint8_t v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v_alreadyFound_2332_ = lean_ctor_get(v_a_2234_, 0);
v_relaxedReuse_2333_ = lean_ctor_get_uint8(v_a_2234_, sizeof(void*)*2);
v_ownedness_2334_ = lean_ctor_get(v_a_2234_, 1);
v___x_2335_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2332_, v_discr_2327_);
v___x_2336_ = 0;
v___x_2337_ = lean_box(v___x_2336_);
v___x_2338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2334_, v_discr_2327_, v___x_2337_);
lean_dec(v___x_2337_);
v___x_2339_ = 1;
v___x_2340_ = lean_unbox(v___x_2338_);
lean_dec(v___x_2338_);
v___x_2341_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2340_, v___x_2339_);
v___x_2342_ = lean_box(0);
lean_inc_n(v_discr_2327_, 2);
lean_inc_ref(v_alreadyFound_2332_);
v___x_2343_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2332_, v_discr_2327_, v___x_2342_);
lean_inc_ref(v_ownedness_2334_);
v___x_2344_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v_ownedness_2334_);
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*2, v_relaxedReuse_2333_);
v_sz_2345_ = lean_array_size(v_alts_2328_);
v___x_2346_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2328_);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2341_, v_discr_2327_, v___x_2335_, v_sz_2345_, v___x_2346_, v_alts_2328_, v___x_2344_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec_ref_known(v___x_2344_, 2);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2372_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2372_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2372_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
size_t v___x_2352_; size_t v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = lean_ptr_addr(v_alts_2328_);
lean_dec_ref(v_alts_2328_);
v___x_2353_ = lean_ptr_addr(v_a_2348_);
v___x_2354_ = lean_usize_dec_eq(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2367_; 
v_isSharedCheck_2367_ = !lean_is_exclusive(v_c_2233_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; 
v_unused_2368_ = lean_ctor_get(v_c_2233_, 0);
lean_dec(v_unused_2368_);
v___x_2356_ = v_c_2233_;
v_isShared_2357_ = v_isSharedCheck_2367_;
goto v_resetjp_2355_;
}
else
{
lean_dec(v_c_2233_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2367_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 3, v_a_2348_);
v___x_2359_ = v___x_2330_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_typeName_2325_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_resultType_2326_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_discr_2327_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_a_2348_);
v___x_2359_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2359_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2361_);
v___x_2363_ = v___x_2350_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v___x_2370_; 
lean_dec(v_a_2348_);
lean_del_object(v___x_2330_);
lean_dec(v_discr_2327_);
lean_dec_ref(v_resultType_2326_);
lean_dec(v_typeName_2325_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_c_2233_);
v___x_2370_ = v___x_2350_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_c_2233_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_del_object(v___x_2330_);
lean_dec_ref(v_alts_2328_);
lean_dec(v_discr_2327_);
lean_dec_ref(v_resultType_2326_);
lean_dec(v_typeName_2325_);
lean_dec_ref_known(v_c_2233_, 1);
v_a_2373_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2347_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2347_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
case 5:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_c_2233_);
return v___x_2382_;
}
case 6:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_c_2233_);
return v___x_2383_;
}
case 8:
{
lean_object* v_fvarId_2384_; lean_object* v_i_2385_; lean_object* v_y_2386_; lean_object* v_k_2387_; lean_object* v___x_2388_; 
v_fvarId_2384_ = lean_ctor_get(v_c_2233_, 0);
v_i_2385_ = lean_ctor_get(v_c_2233_, 1);
v_y_2386_ = lean_ctor_get(v_c_2233_, 2);
v_k_2387_ = lean_ctor_get(v_c_2233_, 3);
lean_inc_ref(v_k_2387_);
v___x_2388_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2387_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2413_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2413_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2413_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
size_t v___x_2393_; size_t v___x_2394_; uint8_t v___x_2395_; 
v___x_2393_ = lean_ptr_addr(v_k_2387_);
v___x_2394_ = lean_ptr_addr(v_a_2389_);
v___x_2395_ = lean_usize_dec_eq(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2405_; 
lean_inc(v_y_2386_);
lean_inc(v_i_2385_);
lean_inc(v_fvarId_2384_);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_c_2233_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; lean_object* v_unused_2407_; lean_object* v_unused_2408_; lean_object* v_unused_2409_; 
v_unused_2406_ = lean_ctor_get(v_c_2233_, 3);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_c_2233_, 2);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_c_2233_, 1);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_c_2233_, 0);
lean_dec(v_unused_2409_);
v___x_2397_ = v_c_2233_;
v_isShared_2398_ = v_isSharedCheck_2405_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v_c_2233_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2405_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 3, v_a_2389_);
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_fvarId_2384_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_i_2385_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_y_2386_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_a_2389_);
v___x_2400_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2402_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2400_);
v___x_2402_ = v___x_2391_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v___x_2411_; 
lean_dec(v_a_2389_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v_c_2233_);
v___x_2411_ = v___x_2391_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_c_2233_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2233_, 4);
return v___x_2388_;
}
}
case 9:
{
lean_object* v_fvarId_2414_; lean_object* v_i_2415_; lean_object* v_offset_2416_; lean_object* v_y_2417_; lean_object* v_ty_2418_; lean_object* v_k_2419_; lean_object* v___x_2420_; 
v_fvarId_2414_ = lean_ctor_get(v_c_2233_, 0);
v_i_2415_ = lean_ctor_get(v_c_2233_, 1);
v_offset_2416_ = lean_ctor_get(v_c_2233_, 2);
v_y_2417_ = lean_ctor_get(v_c_2233_, 3);
v_ty_2418_ = lean_ctor_get(v_c_2233_, 4);
v_k_2419_ = lean_ctor_get(v_c_2233_, 5);
lean_inc_ref(v_k_2419_);
v___x_2420_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2419_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2447_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2447_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2447_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
size_t v___x_2425_; size_t v___x_2426_; uint8_t v___x_2427_; 
v___x_2425_ = lean_ptr_addr(v_k_2419_);
v___x_2426_ = lean_ptr_addr(v_a_2421_);
v___x_2427_ = lean_usize_dec_eq(v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2437_; 
lean_inc_ref(v_ty_2418_);
lean_inc(v_y_2417_);
lean_inc(v_offset_2416_);
lean_inc(v_i_2415_);
lean_inc(v_fvarId_2414_);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_c_2233_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; lean_object* v_unused_2441_; lean_object* v_unused_2442_; lean_object* v_unused_2443_; 
v_unused_2438_ = lean_ctor_get(v_c_2233_, 5);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_c_2233_, 4);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_c_2233_, 3);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_c_2233_, 2);
lean_dec(v_unused_2441_);
v_unused_2442_ = lean_ctor_get(v_c_2233_, 1);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_c_2233_, 0);
lean_dec(v_unused_2443_);
v___x_2429_ = v_c_2233_;
v_isShared_2430_ = v_isSharedCheck_2437_;
goto v_resetjp_2428_;
}
else
{
lean_dec(v_c_2233_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2437_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 5, v_a_2421_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_fvarId_2414_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_i_2415_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_offset_2416_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_y_2417_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_ty_2418_);
lean_ctor_set(v_reuseFailAlloc_2436_, 5, v_a_2421_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2432_);
v___x_2434_ = v___x_2423_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v___x_2445_; 
lean_dec(v_a_2421_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_c_2233_);
v___x_2445_ = v___x_2423_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_c_2233_);
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
lean_dec_ref_known(v_c_2233_, 6);
return v___x_2420_;
}
}
default: 
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec_ref(v_c_2233_);
v___x_2448_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2449_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2448_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2458_, lean_object* v_discr_2459_, uint8_t v___x_2460_, size_t v_sz_2461_, size_t v_i_2462_, lean_object* v_bs_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_usize_dec_lt(v_i_2462_, v_sz_2461_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
lean_dec(v_discr_2459_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_bs_2463_);
return v___x_2471_;
}
else
{
lean_object* v___f_2472_; lean_object* v_v_2473_; lean_object* v___x_2474_; lean_object* v_bs_x27_2475_; lean_object* v_a_2477_; lean_object* v___y_2483_; lean_object* v___x_2493_; 
v___f_2472_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2473_ = lean_array_uget(v_bs_2463_, v_i_2462_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v_bs_x27_2475_ = lean_array_uset(v_bs_2463_, v_i_2462_, v___x_2474_);
v___x_2493_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2473_, v___f_2472_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
if (lean_obj_tag(v_a_2494_) == 1)
{
lean_object* v_info_2495_; lean_object* v_code_2496_; uint8_t v___y_2498_; uint8_t v___x_2510_; 
v_info_2495_ = lean_ctor_get(v_a_2494_, 0);
v_code_2496_ = lean_ctor_get(v_a_2494_, 1);
v___x_2510_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2495_);
if (v___x_2510_ == 0)
{
v___y_2498_ = v___x_2460_;
goto v___jp_2497_;
}
else
{
v___y_2498_ = v___x_2510_;
goto v___jp_2497_;
}
v___jp_2497_:
{
if (v___y_2498_ == 0)
{
if (v___x_2458_ == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref_known(v___x_2493_, 1);
lean_inc_ref(v_code_2496_);
lean_inc_ref(v_info_2495_);
lean_inc(v_discr_2459_);
v___x_2499_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2459_, v_info_2495_, v_code_2496_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2494_, v_a_2500_);
v_a_2477_ = v___x_2501_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec_ref_known(v_a_2494_, 2);
lean_dec_ref(v_bs_x27_2475_);
lean_dec(v_discr_2459_);
v_a_2502_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2499_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2499_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2494_, 2);
v___y_2483_ = v___x_2493_;
goto v___jp_2482_;
}
}
else
{
lean_dec_ref_known(v_a_2494_, 2);
v___y_2483_ = v___x_2493_;
goto v___jp_2482_;
}
}
}
else
{
lean_dec_ref_known(v_a_2494_, 1);
v___y_2483_ = v___x_2493_;
goto v___jp_2482_;
}
}
else
{
v___y_2483_ = v___x_2493_;
goto v___jp_2482_;
}
v___jp_2476_:
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = ((size_t)1ULL);
v___x_2479_ = lean_usize_add(v_i_2462_, v___x_2478_);
v___x_2480_ = lean_array_uset(v_bs_x27_2475_, v_i_2462_, v_a_2477_);
v_i_2462_ = v___x_2479_;
v_bs_2463_ = v___x_2480_;
goto _start;
}
v___jp_2482_:
{
if (lean_obj_tag(v___y_2483_) == 0)
{
lean_object* v_a_2484_; 
v_a_2484_ = lean_ctor_get(v___y_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___y_2483_, 1);
v_a_2477_ = v_a_2484_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_bs_x27_2475_);
lean_dec(v_discr_2459_);
v_a_2485_ = lean_ctor_get(v___y_2483_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___y_2483_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___y_2483_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___y_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2511_, lean_object* v_discr_2512_, lean_object* v___x_2513_, lean_object* v_sz_2514_, lean_object* v_i_2515_, lean_object* v_bs_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v___x_6407__boxed_2523_; uint8_t v___x_6409__boxed_2524_; size_t v_sz_boxed_2525_; size_t v_i_boxed_2526_; lean_object* v_res_2527_; 
v___x_6407__boxed_2523_ = lean_unbox(v___x_2511_);
v___x_6409__boxed_2524_ = lean_unbox(v___x_2513_);
v_sz_boxed_2525_ = lean_unbox_usize(v_sz_2514_);
lean_dec(v_sz_2514_);
v_i_boxed_2526_ = lean_unbox_usize(v_i_2515_);
lean_dec(v_i_2515_);
v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6407__boxed_2523_, v_discr_2512_, v___x_6409__boxed_2524_, v_sz_boxed_2525_, v_i_boxed_2526_, v_bs_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2527_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2528_, lean_object* v_x_2529_, lean_object* v_x_2530_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2529_, v_x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2532_, lean_object* v_x_2533_, lean_object* v_x_2534_){
_start:
{
uint8_t v_res_2535_; lean_object* v_r_2536_; 
v_res_2535_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2532_, v_x_2533_, v_x_2534_);
lean_dec(v_x_2534_);
lean_dec_ref(v_x_2533_);
v_r_2536_ = lean_box(v_res_2535_);
return v_r_2536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2537_, lean_object* v_m_2538_, lean_object* v_a_2539_, lean_object* v_fallback_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2538_, v_a_2539_, v_fallback_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2542_, lean_object* v_m_2543_, lean_object* v_a_2544_, lean_object* v_fallback_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2542_, v_m_2543_, v_a_2544_, v_fallback_2545_);
lean_dec(v_fallback_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_m_2543_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2547_, lean_object* v_x_2548_, lean_object* v_x_2549_, lean_object* v_x_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2548_, v_x_2549_, v_x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2552_, lean_object* v_x_2553_, size_t v_x_2554_, lean_object* v_x_2555_){
_start:
{
uint8_t v___x_2556_; 
v___x_2556_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2553_, v_x_2554_, v_x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_){
_start:
{
size_t v_x_6978__boxed_2561_; uint8_t v_res_2562_; lean_object* v_r_2563_; 
v_x_6978__boxed_2561_ = lean_unbox_usize(v_x_2559_);
lean_dec(v_x_2559_);
v_res_2562_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2557_, v_x_2558_, v_x_6978__boxed_2561_, v_x_2560_);
lean_dec(v_x_2560_);
lean_dec_ref(v_x_2558_);
v_r_2563_ = lean_box(v_res_2562_);
return v_r_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2564_, lean_object* v_a_2565_, lean_object* v_fallback_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2565_, v_fallback_2566_, v_x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2569_, lean_object* v_a_2570_, lean_object* v_fallback_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2569_, v_a_2570_, v_fallback_2571_, v_x_2572_);
lean_dec(v_x_2572_);
lean_dec(v_fallback_2571_);
lean_dec(v_a_2570_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2574_, lean_object* v_x_2575_, size_t v_x_2576_, size_t v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2575_, v_x_2576_, v_x_2577_, v_x_2578_, v_x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
size_t v_x_6994__boxed_2587_; size_t v_x_6995__boxed_2588_; lean_object* v_res_2589_; 
v_x_6994__boxed_2587_ = lean_unbox_usize(v_x_2583_);
lean_dec(v_x_2583_);
v_x_6995__boxed_2588_ = lean_unbox_usize(v_x_2584_);
lean_dec(v_x_2584_);
v_res_2589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2581_, v_x_2582_, v_x_6994__boxed_2587_, v_x_6995__boxed_2588_, v_x_2585_, v_x_2586_);
return v_res_2589_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2590_, lean_object* v_keys_2591_, lean_object* v_vals_2592_, lean_object* v_heq_2593_, lean_object* v_i_2594_, lean_object* v_k_2595_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2591_, v_i_2594_, v_k_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2597_, lean_object* v_keys_2598_, lean_object* v_vals_2599_, lean_object* v_heq_2600_, lean_object* v_i_2601_, lean_object* v_k_2602_){
_start:
{
uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_res_2603_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2597_, v_keys_2598_, v_vals_2599_, v_heq_2600_, v_i_2601_, v_k_2602_);
lean_dec(v_k_2602_);
lean_dec_ref(v_vals_2599_);
lean_dec_ref(v_keys_2598_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2605_, lean_object* v_n_2606_, lean_object* v_k_2607_, lean_object* v_v_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_2606_, v_k_2607_, v_v_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2610_, size_t v_depth_2611_, lean_object* v_keys_2612_, lean_object* v_vals_2613_, lean_object* v_heq_2614_, lean_object* v_i_2615_, lean_object* v_entries_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2611_, v_keys_2612_, v_vals_2613_, v_i_2615_, v_entries_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2618_, lean_object* v_depth_2619_, lean_object* v_keys_2620_, lean_object* v_vals_2621_, lean_object* v_heq_2622_, lean_object* v_i_2623_, lean_object* v_entries_2624_){
_start:
{
size_t v_depth_boxed_2625_; lean_object* v_res_2626_; 
v_depth_boxed_2625_ = lean_unbox_usize(v_depth_2619_);
lean_dec(v_depth_2619_);
v_res_2626_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_2618_, v_depth_boxed_2625_, v_keys_2620_, v_vals_2621_, v_heq_2622_, v_i_2623_, v_entries_2624_);
lean_dec_ref(v_vals_2621_);
lean_dec_ref(v_keys_2620_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2628_, v_x_2629_, v_x_2630_, v_x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v_toApplicative_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2706_; 
v___x_2642_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2643_ = l_StateRefT_x27_instMonad___redArg(v___x_2642_);
v_toApplicative_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2643_, 1);
lean_dec(v_unused_2707_);
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2706_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_toApplicative_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2706_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_toFunctor_2648_; lean_object* v_toSeq_2649_; lean_object* v_toSeqLeft_2650_; lean_object* v_toSeqRight_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2704_; 
v_toFunctor_2648_ = lean_ctor_get(v_toApplicative_2644_, 0);
v_toSeq_2649_ = lean_ctor_get(v_toApplicative_2644_, 2);
v_toSeqLeft_2650_ = lean_ctor_get(v_toApplicative_2644_, 3);
v_toSeqRight_2651_ = lean_ctor_get(v_toApplicative_2644_, 4);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_toApplicative_2644_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_toApplicative_2644_, 1);
lean_dec(v_unused_2705_);
v___x_2653_ = v_toApplicative_2644_;
v_isShared_2654_ = v_isSharedCheck_2704_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_toSeqRight_2651_);
lean_inc(v_toSeqLeft_2650_);
lean_inc(v_toSeq_2649_);
lean_inc(v_toFunctor_2648_);
lean_dec(v_toApplicative_2644_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2704_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___f_2655_; lean_object* v___f_2656_; lean_object* v___f_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___f_2660_; lean_object* v___f_2661_; lean_object* v___f_2662_; lean_object* v___x_2664_; 
v___f_2655_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2656_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2648_);
v___f_2657_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2657_, 0, v_toFunctor_2648_);
v___f_2658_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2658_, 0, v_toFunctor_2648_);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___f_2657_);
lean_ctor_set(v___x_2659_, 1, v___f_2658_);
v___f_2660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2660_, 0, v_toSeqRight_2651_);
v___f_2661_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2661_, 0, v_toSeqLeft_2650_);
v___f_2662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2662_, 0, v_toSeq_2649_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 4, v___f_2660_);
lean_ctor_set(v___x_2653_, 3, v___f_2661_);
lean_ctor_set(v___x_2653_, 2, v___f_2662_);
lean_ctor_set(v___x_2653_, 1, v___f_2655_);
lean_ctor_set(v___x_2653_, 0, v___x_2659_);
v___x_2664_ = v___x_2653_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___f_2655_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v___f_2662_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v___f_2661_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v___f_2660_);
v___x_2664_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2666_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___f_2656_);
lean_ctor_set(v___x_2646_, 0, v___x_2664_);
v___x_2666_ = v___x_2646_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___f_2656_);
v___x_2666_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v_toApplicative_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2700_; 
v___x_2667_ = l_StateRefT_x27_instMonad___redArg(v___x_2666_);
v_toApplicative_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2667_, 1);
lean_dec(v_unused_2701_);
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2700_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_toApplicative_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2700_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_toFunctor_2672_; lean_object* v_toSeq_2673_; lean_object* v_toSeqLeft_2674_; lean_object* v_toSeqRight_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2698_; 
v_toFunctor_2672_ = lean_ctor_get(v_toApplicative_2668_, 0);
v_toSeq_2673_ = lean_ctor_get(v_toApplicative_2668_, 2);
v_toSeqLeft_2674_ = lean_ctor_get(v_toApplicative_2668_, 3);
v_toSeqRight_2675_ = lean_ctor_get(v_toApplicative_2668_, 4);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_toApplicative_2668_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v_toApplicative_2668_, 1);
lean_dec(v_unused_2699_);
v___x_2677_ = v_toApplicative_2668_;
v_isShared_2678_ = v_isSharedCheck_2698_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_toSeqRight_2675_);
lean_inc(v_toSeqLeft_2674_);
lean_inc(v_toSeq_2673_);
lean_inc(v_toFunctor_2672_);
lean_dec(v_toApplicative_2668_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2698_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___f_2679_; lean_object* v___f_2680_; lean_object* v___f_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___f_2686_; lean_object* v___x_2688_; 
v___f_2679_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2680_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2672_);
v___f_2681_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2681_, 0, v_toFunctor_2672_);
v___f_2682_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2682_, 0, v_toFunctor_2672_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___f_2681_);
lean_ctor_set(v___x_2683_, 1, v___f_2682_);
v___f_2684_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2684_, 0, v_toSeqRight_2675_);
v___f_2685_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2685_, 0, v_toSeqLeft_2674_);
v___f_2686_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2686_, 0, v_toSeq_2673_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 4, v___f_2684_);
lean_ctor_set(v___x_2677_, 3, v___f_2685_);
lean_ctor_set(v___x_2677_, 2, v___f_2686_);
lean_ctor_set(v___x_2677_, 1, v___f_2679_);
lean_ctor_set(v___x_2677_, 0, v___x_2683_);
v___x_2688_ = v___x_2677_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___f_2679_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v___f_2686_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v___f_2685_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v___f_2684_);
v___x_2688_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2690_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___f_2680_);
lean_ctor_set(v___x_2670_, 0, v___x_2688_);
v___x_2690_ = v___x_2670_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___f_2680_);
v___x_2690_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2546__overap_2694_; lean_object* v___x_2695_; 
v___x_2691_ = l_StateRefT_x27_instMonad___redArg(v___x_2690_);
v___x_2692_ = lean_box(0);
v___x_2693_ = l_instInhabitedOfMonad___redArg(v___x_2691_, v___x_2692_);
v___x_2546__overap_2694_ = lean_panic_fn_borrowed(v___x_2693_, v_msg_2635_);
lean_dec(v___x_2693_);
lean_inc(v___y_2640_);
lean_inc_ref(v___y_2639_);
lean_inc(v___y_2638_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
v___x_2695_ = lean_apply_6(v___x_2546__overap_2694_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, lean_box(0));
return v___x_2695_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
return v_res_2715_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2718_ = lean_unsigned_to_nat(61u);
v___x_2719_ = lean_unsigned_to_nat(304u);
v___x_2720_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2721_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2722_ = l_mkPanicMessageWithDecl(v___x_2721_, v___x_2720_, v___x_2719_, v___x_2718_, v___x_2717_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
switch(lean_obj_tag(v_c_2723_))
{
case 0:
{
lean_object* v_decl_2730_; lean_object* v_value_2731_; 
v_decl_2730_ = lean_ctor_get(v_c_2723_, 0);
v_value_2731_ = lean_ctor_get(v_decl_2730_, 3);
if (lean_obj_tag(v_value_2731_) == 11)
{
lean_object* v_k_2732_; lean_object* v_var_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_inc_ref(v_value_2731_);
v_k_2732_ = lean_ctor_get(v_c_2723_, 1);
lean_inc_ref(v_k_2732_);
lean_dec_ref_known(v_c_2723_, 2);
v_var_2733_ = lean_ctor_get(v_value_2731_, 1);
lean_inc(v_var_2733_);
lean_dec_ref_known(v_value_2731_, 2);
v___x_2734_ = lean_st_ref_take(v_a_2724_);
v___x_2735_ = lean_box(0);
v___x_2736_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2734_, v_var_2733_, v___x_2735_);
v___x_2737_ = lean_st_ref_put(v_a_2724_, v___x_2736_);
v_c_2723_ = v_k_2732_;
goto _start;
}
else
{
lean_object* v_k_2739_; 
v_k_2739_ = lean_ctor_get(v_c_2723_, 1);
lean_inc_ref(v_k_2739_);
lean_dec_ref_known(v_c_2723_, 2);
v_c_2723_ = v_k_2739_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2741_; lean_object* v_k_2742_; lean_object* v_value_2743_; lean_object* v___x_2744_; 
v_decl_2741_ = lean_ctor_get(v_c_2723_, 0);
lean_inc_ref(v_decl_2741_);
v_k_2742_ = lean_ctor_get(v_c_2723_, 1);
lean_inc_ref(v_k_2742_);
lean_dec_ref_known(v_c_2723_, 2);
v_value_2743_ = lean_ctor_get(v_decl_2741_, 4);
lean_inc_ref(v_value_2743_);
lean_dec_ref(v_decl_2741_);
v___x_2744_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2743_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_dec_ref_known(v___x_2744_, 1);
v_c_2723_ = v_k_2742_;
goto _start;
}
else
{
lean_dec_ref(v_k_2742_);
return v___x_2744_;
}
}
case 3:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_dec_ref_known(v_c_2723_, 2);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
case 4:
{
lean_object* v_cases_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2770_; 
v_cases_2748_ = lean_ctor_get(v_c_2723_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_c_2723_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2750_ = v_c_2723_;
v_isShared_2751_ = v_isSharedCheck_2770_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_cases_2748_);
lean_dec(v_c_2723_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2770_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_alts_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_alts_2752_ = lean_ctor_get(v_cases_2748_, 3);
lean_inc_ref(v_alts_2752_);
lean_dec_ref(v_cases_2748_);
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = lean_array_get_size(v_alts_2752_);
v___x_2755_ = lean_box(0);
v___x_2756_ = lean_nat_dec_lt(v___x_2753_, v___x_2754_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2758_; 
lean_dec_ref(v_alts_2752_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2755_);
v___x_2758_ = v___x_2750_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
else
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_nat_dec_le(v___x_2754_, v___x_2754_);
if (v___x_2760_ == 0)
{
if (v___x_2756_ == 0)
{
lean_object* v___x_2762_; 
lean_dec_ref(v_alts_2752_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2755_);
v___x_2762_ = v___x_2750_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2755_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
else
{
size_t v___x_2764_; size_t v___x_2765_; lean_object* v___x_2766_; 
lean_del_object(v___x_2750_);
v___x_2764_ = ((size_t)0ULL);
v___x_2765_ = lean_usize_of_nat(v___x_2754_);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2752_, v___x_2764_, v___x_2765_, v___x_2755_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec_ref(v_alts_2752_);
return v___x_2766_;
}
}
else
{
size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; 
lean_del_object(v___x_2750_);
v___x_2767_ = ((size_t)0ULL);
v___x_2768_ = lean_usize_of_nat(v___x_2754_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2752_, v___x_2767_, v___x_2768_, v___x_2755_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec_ref(v_alts_2752_);
return v___x_2769_;
}
}
}
}
case 5:
{
lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2778_; 
v_isSharedCheck_2778_ = !lean_is_exclusive(v_c_2723_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; 
v_unused_2779_ = lean_ctor_get(v_c_2723_, 0);
lean_dec(v_unused_2779_);
v___x_2772_ = v_c_2723_;
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v_c_2723_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_box(0);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
case 6:
{
lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2787_; 
v_isSharedCheck_2787_ = !lean_is_exclusive(v_c_2723_);
if (v_isSharedCheck_2787_ == 0)
{
lean_object* v_unused_2788_; 
v_unused_2788_ = lean_ctor_get(v_c_2723_, 0);
lean_dec(v_unused_2788_);
v___x_2781_ = v_c_2723_;
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
else
{
lean_dec(v_c_2723_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2783_ = lean_box(0);
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2783_);
v___x_2785_ = v___x_2781_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
case 8:
{
lean_object* v_k_2789_; 
v_k_2789_ = lean_ctor_get(v_c_2723_, 3);
lean_inc_ref(v_k_2789_);
lean_dec_ref_known(v_c_2723_, 4);
v_c_2723_ = v_k_2789_;
goto _start;
}
case 9:
{
lean_object* v_k_2791_; 
v_k_2791_ = lean_ctor_get(v_c_2723_, 5);
lean_inc_ref(v_k_2791_);
lean_dec_ref_known(v_c_2723_, 6);
v_c_2723_ = v_k_2791_;
goto _start;
}
default: 
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_c_2723_);
v___x_2793_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2794_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2793_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2795_, size_t v_i_2796_, size_t v_stop_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v___y_2806_; uint8_t v___x_2812_; 
v___x_2812_ = lean_usize_dec_eq(v_i_2796_, v_stop_2797_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_array_uget_borrowed(v_as_2795_, v_i_2796_);
switch(lean_obj_tag(v___x_2813_))
{
case 0:
{
lean_object* v_code_2814_; 
v_code_2814_ = lean_ctor_get(v___x_2813_, 2);
lean_inc_ref(v_code_2814_);
v___y_2806_ = v_code_2814_;
goto v___jp_2805_;
}
case 1:
{
lean_object* v_code_2815_; 
v_code_2815_ = lean_ctor_get(v___x_2813_, 1);
lean_inc_ref(v_code_2815_);
v___y_2806_ = v_code_2815_;
goto v___jp_2805_;
}
default: 
{
lean_object* v_code_2816_; 
v_code_2816_ = lean_ctor_get(v___x_2813_, 0);
lean_inc_ref(v_code_2816_);
v___y_2806_ = v_code_2816_;
goto v___jp_2805_;
}
}
}
else
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_b_2798_);
return v___x_2817_;
}
v___jp_2805_:
{
lean_object* v___x_2807_; 
v___x_2807_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2806_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; size_t v___x_2809_; size_t v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_add(v_i_2796_, v___x_2809_);
v_i_2796_ = v___x_2810_;
v_b_2798_ = v_a_2808_;
goto _start;
}
else
{
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2818_, lean_object* v_i_2819_, lean_object* v_stop_2820_, lean_object* v_b_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
size_t v_i_boxed_2828_; size_t v_stop_boxed_2829_; lean_object* v_res_2830_; 
v_i_boxed_2828_ = lean_unbox_usize(v_i_2819_);
lean_dec(v_i_2819_);
v_stop_boxed_2829_ = lean_unbox_usize(v_stop_2820_);
lean_dec(v_stop_2820_);
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2818_, v_i_boxed_2828_, v_stop_boxed_2829_, v_b_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v_as_2818_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
return v_res_2838_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2839_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__0);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg(){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___closed__1);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg___boxed(lean_object* v___dummy_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
return v_res_2845_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___redArg();
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2849_, lean_object* v_v_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
if (lean_obj_tag(v_v_2850_) == 0)
{
lean_object* v_code_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2881_; 
v_code_2857_ = lean_ctor_get(v_v_2850_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_v_2850_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2859_ = v_v_2850_;
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_code_2857_);
lean_dec(v_v_2850_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; 
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
lean_inc_ref(v___y_2851_);
v___x_2861_ = lean_apply_7(v_f_2849_, v_code_2857_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, lean_box(0));
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2872_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2872_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2872_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_a_2862_);
v___x_2867_ = v___x_2859_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2867_);
v___x_2869_ = v___x_2864_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_del_object(v___x_2859_);
v_a_2873_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2861_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2861_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v___x_2882_; 
lean_dec_ref(v_f_2849_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_v_2850_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2883_, lean_object* v_v_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2883_, v_v_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2892_, lean_object* v_f_2893_, lean_object* v_v_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2893_, v_v_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2902_, lean_object* v_f_2903_, lean_object* v_v_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v_pu_boxed_2911_; lean_object* v_res_2912_; 
v_pu_boxed_2911_ = lean_unbox(v_pu_2902_);
v_res_2912_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_2911_, v_f_2903_, v_v_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_alreadyFound_2921_; uint8_t v_relaxedReuse_2922_; lean_object* v_ownedness_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v_relaxedReuse_2930_; 
v_relaxedReuse_2930_ = lean_ctor_get_uint8(v___y_2914_, sizeof(void*)*2);
if (v_relaxedReuse_2930_ == 0)
{
lean_object* v_ownedness_2931_; lean_object* v___x_2932_; 
v_ownedness_2931_ = lean_ctor_get(v___y_2914_, 1);
v___x_2932_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v_alreadyFound_2921_ = v___x_2932_;
v_relaxedReuse_2922_ = v_relaxedReuse_2930_;
v_ownedness_2923_ = v_ownedness_2931_;
v___y_2924_ = v___y_2915_;
v___y_2925_ = v___y_2916_;
v___y_2926_ = v___y_2917_;
v___y_2927_ = v___y_2918_;
goto v___jp_2920_;
}
else
{
lean_object* v_ownedness_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_ownedness_2933_ = lean_ctor_get(v___y_2914_, 1);
v___x_2934_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2935_ = lean_st_mk_ref(v___x_2934_);
lean_inc_ref(v_code_2913_);
v___x_2936_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_2913_, v___x_2935_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2937_; 
lean_dec_ref_known(v___x_2936_, 1);
v___x_2937_ = lean_st_ref_get(v___x_2935_);
lean_dec(v___x_2935_);
v_alreadyFound_2921_ = v___x_2937_;
v_relaxedReuse_2922_ = v_relaxedReuse_2930_;
v_ownedness_2923_ = v_ownedness_2933_;
v___y_2924_ = v___y_2915_;
v___y_2925_ = v___y_2916_;
v___y_2926_ = v___y_2917_;
v___y_2927_ = v___y_2918_;
goto v___jp_2920_;
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v___x_2935_);
lean_dec_ref(v_code_2913_);
v_a_2938_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2936_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2936_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
v___jp_2920_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_inc_ref(v_ownedness_2923_);
v___x_2928_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2928_, 0, v_alreadyFound_2921_);
lean_ctor_set(v___x_2928_, 1, v_ownedness_2923_);
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*2, v_relaxedReuse_2922_);
v___x_2929_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_2913_, v___x_2928_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec_ref_known(v___x_2928_, 2);
return v___x_2929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_toSignature_2962_; lean_object* v_value_2963_; uint8_t v_recursive_2964_; lean_object* v_inlineAttr_x3f_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2990_; 
v_toSignature_2962_ = lean_ctor_get(v_decl_2955_, 0);
v_value_2963_ = lean_ctor_get(v_decl_2955_, 1);
v_recursive_2964_ = lean_ctor_get_uint8(v_decl_2955_, sizeof(void*)*3);
v_inlineAttr_x3f_2965_ = lean_ctor_get(v_decl_2955_, 2);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_decl_2955_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2967_ = v_decl_2955_;
v_isShared_2968_ = v_isSharedCheck_2990_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_inlineAttr_x3f_2965_);
lean_inc(v_value_2963_);
lean_inc(v_toSignature_2962_);
lean_dec(v_decl_2955_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2990_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___f_2969_; lean_object* v___x_2970_; 
v___f_2969_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_2970_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_2969_, v_value_2963_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2981_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2981_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 1, v_a_2971_);
v___x_2976_ = v___x_2967_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_toSignature_2962_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_a_2971_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_inlineAttr_x3f_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*3, v_recursive_2964_);
v___x_2976_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2978_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2976_);
v___x_2978_ = v___x_2973_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_del_object(v___x_2967_);
lean_dec(v_inlineAttr_x3f_2965_);
lean_dec_ref(v_toSignature_2962_);
v_a_2982_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2970_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2970_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec_ref(v_a_2992_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3000_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3033_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3033_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3033_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
uint8_t v_resetReuse_3010_; 
v_resetReuse_3010_ = lean_ctor_get_uint8(v_a_3006_, sizeof(void*)*4 + 2);
lean_dec(v_a_3006_);
if (v_resetReuse_3010_ == 0)
{
lean_object* v___x_3012_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v_decl_2999_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_decl_2999_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
else
{
lean_object* v___x_3014_; 
lean_del_object(v___x_3008_);
lean_inc_ref(v_decl_2999_);
v___x_3014_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc_n(v_a_3015_, 2);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_2999_, v_a_3015_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_3019_ = 0;
lean_inc(v_a_3015_);
v___x_3020_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v_a_3015_);
lean_ctor_set_uint8(v___x_3020_, sizeof(void*)*2, v___x_3019_);
v___x_3021_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3017_, v___x_3020_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
lean_dec_ref_known(v___x_3020_, 2);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3023_, 0, v___x_3018_);
lean_ctor_set(v___x_3023_, 1, v_a_3015_);
lean_ctor_set_uint8(v___x_3023_, sizeof(void*)*2, v_resetReuse_3010_);
v___x_3024_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3022_, v___x_3023_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_);
lean_dec_ref_known(v___x_3023_, 2);
return v___x_3024_;
}
else
{
lean_dec(v_a_3015_);
return v___x_3021_;
}
}
else
{
lean_dec(v_a_3015_);
return v___x_3016_;
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_decl_2999_);
v_a_3025_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3014_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3014_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v_decl_2999_);
v_a_3034_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3005_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3005_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
return v_res_3048_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3053_ = lean_unsigned_to_nat(0u);
v___x_3054_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3055_ = 2;
v___x_3056_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3057_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3056_, v___x_3055_, v___x_3054_, v___x_3053_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3058_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_unsigned_to_nat(2506150707u);
v___x_3115_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3116_ = l_Lean_Name_num___override(v___x_3115_, v___x_3114_);
return v___x_3116_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3119_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3120_ = l_Lean_Name_str___override(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3123_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3124_ = l_Lean_Name_str___override(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_unsigned_to_nat(2u);
v___x_3126_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3127_ = l_Lean_Name_num___override(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3129_; uint8_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3129_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3130_ = 1;
v___x_3131_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3132_ = l_Lean_registerTraceClass(v___x_3129_, v___x_3130_, v___x_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3134_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_insertResetReuse = _init_l_Lean_Compiler_LCNF_insertResetReuse();
lean_mark_persistent(l_Lean_Compiler_LCNF_insertResetReuse);
res = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LiveVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PropagateBorrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
}
#ifdef __cplusplus
}
#endif
