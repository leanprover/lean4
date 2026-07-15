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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0;
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
lean_object* v_name_5_; lean_object* v_size_6_; lean_object* v_usize_7_; lean_object* v_ssize_8_; lean_object* v_name_9_; lean_object* v_size_10_; lean_object* v_usize_11_; lean_object* v_ssize_12_; uint8_t v___y_14_; uint8_t v___x_28_; 
v_name_5_ = lean_ctor_get(v_c_u2081_1_, 0);
v_size_6_ = lean_ctor_get(v_c_u2081_1_, 2);
v_usize_7_ = lean_ctor_get(v_c_u2081_1_, 3);
v_ssize_8_ = lean_ctor_get(v_c_u2081_1_, 4);
v_name_9_ = lean_ctor_get(v_c_u2082_2_, 0);
v_size_10_ = lean_ctor_get(v_c_u2082_2_, 2);
v_usize_11_ = lean_ctor_get(v_c_u2082_2_, 3);
v_ssize_12_ = lean_ctor_get(v_c_u2082_2_, 4);
v___x_28_ = lean_nat_dec_eq(v_size_6_, v_size_10_);
if (v___x_28_ == 0)
{
v___y_14_ = v___x_28_;
goto v___jp_13_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = lean_nat_dec_eq(v_usize_7_, v_usize_11_);
v___y_14_ = v___x_29_;
goto v___jp_13_;
}
v___jp_13_:
{
if (v___y_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(v___y_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = lean_nat_dec_eq(v_ssize_8_, v_ssize_12_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_box(v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
else
{
uint8_t v_relaxedReuse_20_; 
v_relaxedReuse_20_ = lean_ctor_get_uint8(v_a_3_, sizeof(void*)*2);
if (v_relaxedReuse_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_21_ = l_Lean_Name_getPrefix(v_name_5_);
v___x_22_ = l_Lean_Name_getPrefix(v_name_9_);
v___x_23_ = lean_name_eq(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_box(v_relaxedReuse_20_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
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
uint8_t v___x_53_; lean_object* v___x_54_; 
v___x_53_ = 1;
v___x_54_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(lean_object* v_msg_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_57_ = lean_panic_fn_borrowed(v___x_56_, v_msg_55_);
return v___x_57_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_instMonadEIO(lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_toApplicative_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_107_; 
v___x_68_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_69_ = l_StateRefT_x27_instMonad___redArg(v___x_68_);
v_toApplicative_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v___x_69_, 1);
lean_dec(v_unused_108_);
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_107_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_toApplicative_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_107_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_toFunctor_74_; lean_object* v_toSeq_75_; lean_object* v_toSeqLeft_76_; lean_object* v_toSeqRight_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_105_; 
v_toFunctor_74_ = lean_ctor_get(v_toApplicative_70_, 0);
v_toSeq_75_ = lean_ctor_get(v_toApplicative_70_, 2);
v_toSeqLeft_76_ = lean_ctor_get(v_toApplicative_70_, 3);
v_toSeqRight_77_ = lean_ctor_get(v_toApplicative_70_, 4);
v_isSharedCheck_105_ = !lean_is_exclusive(v_toApplicative_70_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v_toApplicative_70_, 1);
lean_dec(v_unused_106_);
v___x_79_ = v_toApplicative_70_;
v_isShared_80_ = v_isSharedCheck_105_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_toSeqRight_77_);
lean_inc(v_toSeqLeft_76_);
lean_inc(v_toSeq_75_);
lean_inc(v_toFunctor_74_);
lean_dec(v_toApplicative_70_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_105_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_90_; 
v___f_81_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_82_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_74_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_74_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_84_, 0, v_toFunctor_74_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___f_83_);
lean_ctor_set(v___x_85_, 1, v___f_84_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeqRight_77_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeqLeft_76_);
v___f_88_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_88_, 0, v_toSeq_75_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 4, v___f_86_);
lean_ctor_set(v___x_79_, 3, v___f_87_);
lean_ctor_set(v___x_79_, 2, v___f_88_);
lean_ctor_set(v___x_79_, 1, v___f_81_);
lean_ctor_set(v___x_79_, 0, v___x_85_);
v___x_90_ = v___x_79_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___f_81_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v___f_88_);
lean_ctor_set(v_reuseFailAlloc_104_, 3, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_104_, 4, v___f_86_);
v___x_90_ = v_reuseFailAlloc_104_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_92_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___f_82_);
lean_ctor_set(v___x_72_, 0, v___x_90_);
v___x_92_ = v___x_72_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___f_82_);
v___x_92_ = v_reuseFailAlloc_103_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_3796__overap_101_; lean_object* v___x_102_; 
v___x_93_ = l_StateRefT_x27_instMonad___redArg(v___x_92_);
v___x_94_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_95_ = 0;
v___x_96_ = lean_box(v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_94_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = l_instInhabitedOfMonad___redArg(v___x_93_, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_99_, 0, v___x_98_);
v___f_100_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_100_, 0, v___f_99_);
v___x_3796__overap_101_ = lean_panic_fn_borrowed(v___f_100_, v_msg_61_);
lean_dec_ref(v___f_100_);
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc_ref(v___y_62_);
v___x_102_ = lean_apply_6(v___x_3796__overap_101_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, lean_box(0));
return v___x_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___boxed(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(lean_object* v_as_117_, size_t v_i_118_, size_t v_stop_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_eq(v_i_118_, v_stop_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_uget_borrowed(v_as_117_, v_i_118_);
v___x_122_ = lean_unbox(v___x_121_);
if (v___x_122_ == 0)
{
size_t v___x_123_; size_t v___x_124_; 
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_i_118_, v___x_123_);
v_i_118_ = v___x_124_;
goto _start;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_unbox(v___x_121_);
return v___x_126_;
}
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2___boxed(lean_object* v_as_128_, lean_object* v_i_129_, lean_object* v_stop_130_){
_start:
{
size_t v_i_boxed_131_; size_t v_stop_boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_i_boxed_131_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_stop_boxed_132_ = lean_unbox_usize(v_stop_130_);
lean_dec(v_stop_130_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_as_128_, v_i_boxed_131_, v_stop_boxed_132_);
lean_dec_ref(v_as_128_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_139_ = lean_unsigned_to_nat(9u);
v___x_140_ = lean_unsigned_to_nat(633u);
v___x_141_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__1));
v___x_142_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__0));
v___x_143_ = l_mkPanicMessageWithDecl(v___x_142_, v___x_141_, v___x_140_, v___x_139_, v___x_138_);
return v___x_143_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_147_ = lean_unsigned_to_nat(61u);
v___x_148_ = lean_unsigned_to_nat(125u);
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__5));
v___x_150_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_151_ = l_mkPanicMessageWithDecl(v___x_150_, v___x_149_, v___x_148_, v___x_147_, v___x_146_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(lean_object* v_info_152_, lean_object* v_w_153_, lean_object* v_c_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
uint8_t v___y_162_; lean_object* v___y_163_; lean_object* v_k_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; 
switch(lean_obj_tag(v_c_154_))
{
case 0:
{
lean_object* v_decl_388_; lean_object* v_value_389_; 
v_decl_388_ = lean_ctor_get(v_c_154_, 0);
lean_inc_ref(v_decl_388_);
v_value_389_ = lean_ctor_get(v_decl_388_, 3);
lean_inc(v_value_389_);
if (lean_obj_tag(v_value_389_) == 5)
{
lean_object* v_k_390_; lean_object* v_fvarId_391_; lean_object* v_binderName_392_; lean_object* v_type_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_456_; 
v_k_390_ = lean_ctor_get(v_c_154_, 1);
v_fvarId_391_ = lean_ctor_get(v_decl_388_, 0);
v_binderName_392_ = lean_ctor_get(v_decl_388_, 1);
v_type_393_ = lean_ctor_get(v_decl_388_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_decl_388_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_decl_388_, 3);
lean_dec(v_unused_457_);
v___x_395_ = v_decl_388_;
v_isShared_396_ = v_isSharedCheck_456_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_type_393_);
lean_inc(v_binderName_392_);
lean_inc(v_fvarId_391_);
lean_dec(v_decl_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_456_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_i_397_; lean_object* v_args_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_455_; 
v_i_397_ = lean_ctor_get(v_value_389_, 0);
v_args_398_ = lean_ctor_get(v_value_389_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_value_389_);
if (v_isSharedCheck_455_ == 0)
{
v___x_400_ = v_value_389_;
v_isShared_401_ = v_isSharedCheck_455_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_args_398_);
lean_inc(v_i_397_);
lean_dec(v_value_389_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_455_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; 
v___x_402_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_mayReuse___redArg(v_info_152_, v_i_397_, v_a_155_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; uint8_t v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = lean_unbox(v_a_403_);
if (v___x_404_ == 0)
{
lean_dec(v_a_403_);
lean_del_object(v___x_400_);
lean_dec_ref(v_args_398_);
lean_dec_ref(v_i_397_);
lean_del_object(v___x_395_);
lean_dec_ref(v_type_393_);
lean_dec(v_binderName_392_);
lean_dec(v_fvarId_391_);
lean_inc_ref(v_k_390_);
v_k_168_ = v_k_390_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_444_; 
lean_inc_ref(v_k_390_);
v_isSharedCheck_444_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_446_);
v___x_406_ = v_c_154_;
v_isShared_407_ = v_isSharedCheck_444_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_c_154_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_444_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_cidx_408_; lean_object* v_cidx_409_; uint8_t v___x_410_; lean_object* v___x_412_; 
v_cidx_408_ = lean_ctor_get(v_info_152_, 1);
v_cidx_409_ = lean_ctor_get(v_i_397_, 1);
v___x_410_ = 1;
lean_inc_ref(v_args_398_);
lean_inc_ref(v_i_397_);
if (v_isShared_401_ == 0)
{
v___x_412_ = v___x_400_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_i_397_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_args_398_);
v___x_412_ = v_reuseFailAlloc_443_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; 
lean_inc_ref(v_type_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 3, v___x_412_);
v___x_414_ = v___x_395_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_fvarId_391_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_binderName_392_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_type_393_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v___x_412_);
v___x_414_ = v_reuseFailAlloc_442_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
uint8_t v___y_416_; uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_eq(v_cidx_408_, v_cidx_409_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = lean_unbox(v_a_403_);
v___y_416_ = v___x_440_;
goto v___jp_415_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = 0;
v___y_416_ = v___x_441_;
goto v___jp_415_;
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(v___x_417_, 0, v_w_153_);
lean_ctor_set(v___x_417_, 1, v_i_397_);
lean_ctor_set(v___x_417_, 2, v_args_398_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*3, v___y_416_);
v___x_418_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_410_, v___x_414_, v_type_393_, v___x_417_, v_a_157_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_430_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_a_419_);
v___x_424_ = v___x_406_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_k_390_);
v___x_424_ = v_reuseFailAlloc_429_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v_a_403_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
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
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_del_object(v___x_406_);
lean_dec(v_a_403_);
lean_dec_ref(v_k_390_);
v_a_431_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_418_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_418_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
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
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_del_object(v___x_400_);
lean_dec_ref(v_args_398_);
lean_dec_ref(v_i_397_);
lean_del_object(v___x_395_);
lean_dec_ref(v_type_393_);
lean_dec(v_binderName_392_);
lean_dec(v_fvarId_391_);
lean_dec_ref_known(v_c_154_, 2);
lean_dec(v_w_153_);
v_a_447_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_402_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_402_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
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
}
}
else
{
lean_object* v_k_458_; 
lean_dec(v_value_389_);
lean_dec_ref(v_decl_388_);
v_k_458_ = lean_ctor_get(v_c_154_, 1);
lean_inc_ref(v_k_458_);
v_k_168_ = v_k_458_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
}
case 2:
{
lean_object* v_decl_459_; lean_object* v_k_460_; lean_object* v_params_461_; lean_object* v_type_462_; lean_object* v_value_463_; lean_object* v___x_464_; 
v_decl_459_ = lean_ctor_get(v_c_154_, 0);
v_k_460_ = lean_ctor_get(v_c_154_, 1);
v_params_461_ = lean_ctor_get(v_decl_459_, 2);
v_type_462_ = lean_ctor_get(v_decl_459_, 3);
v_value_463_ = lean_ctor_get(v_decl_459_, 4);
lean_inc_ref(v_value_463_);
lean_inc(v_w_153_);
v___x_464_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_152_, v_w_153_, v_value_463_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v_snd_466_; uint8_t v___x_467_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v_snd_466_ = lean_ctor_get(v_a_465_, 1);
lean_inc(v_snd_466_);
v___x_467_ = lean_unbox(v_snd_466_);
if (v___x_467_ == 0)
{
lean_dec(v_snd_466_);
lean_dec(v_a_465_);
lean_inc_ref(v_k_460_);
v_k_168_ = v_k_460_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
else
{
lean_object* v_fst_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_511_; 
lean_dec(v_w_153_);
v_fst_468_ = lean_ctor_get(v_a_465_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_465_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_a_465_, 1);
lean_dec(v_unused_512_);
v___x_470_ = v_a_465_;
v_isShared_471_ = v_isSharedCheck_511_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_fst_468_);
lean_dec(v_a_465_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_511_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; lean_object* v___x_473_; 
v___x_472_ = 1;
lean_inc_ref(v_params_461_);
lean_inc_ref(v_type_462_);
lean_inc_ref(v_decl_459_);
v___x_473_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_472_, v_decl_459_, v_type_462_, v_params_461_, v_fst_468_, v_a_157_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_502_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_502_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_502_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_502_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___y_479_; uint8_t v___y_487_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_ptr_addr(v_k_460_);
v___x_498_ = lean_usize_dec_eq(v___x_497_, v___x_497_);
if (v___x_498_ == 0)
{
v___y_487_ = v___x_498_;
goto v___jp_486_;
}
else
{
size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_ptr_addr(v_decl_459_);
v___x_500_ = lean_ptr_addr(v_a_474_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
v___y_487_ = v___x_501_;
goto v___jp_486_;
}
v___jp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___y_479_);
v___x_481_ = v___x_470_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___y_479_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_snd_466_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_481_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_inc_ref(v_k_460_);
v_isSharedCheck_494_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_495_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_496_);
v___x_489_ = v_c_154_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_c_154_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v_a_474_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_460_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v___y_479_ = v___x_492_;
goto v___jp_478_;
}
}
}
else
{
lean_dec(v_a_474_);
v___y_479_ = v_c_154_;
goto v___jp_478_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_del_object(v___x_470_);
lean_dec(v_snd_466_);
lean_dec_ref_known(v_c_154_, 2);
v_a_503_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_473_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_473_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_c_154_, 2);
lean_dec(v_w_153_);
return v___x_464_;
}
}
case 3:
{
uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_w_153_);
v___x_513_ = 0;
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_c_154_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
case 4:
{
lean_object* v_cases_517_; lean_object* v_typeName_518_; lean_object* v_resultType_519_; lean_object* v_discr_520_; lean_object* v_alts_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_573_; 
v_cases_517_ = lean_ctor_get(v_c_154_, 0);
lean_inc_ref(v_cases_517_);
v_typeName_518_ = lean_ctor_get(v_cases_517_, 0);
v_resultType_519_ = lean_ctor_get(v_cases_517_, 1);
v_discr_520_ = lean_ctor_get(v_cases_517_, 2);
v_alts_521_ = lean_ctor_get(v_cases_517_, 3);
v_isSharedCheck_573_ = !lean_is_exclusive(v_cases_517_);
if (v_isSharedCheck_573_ == 0)
{
v___x_523_ = v_cases_517_;
v_isShared_524_ = v_isSharedCheck_573_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_alts_521_);
lean_inc(v_discr_520_);
lean_inc(v_resultType_519_);
lean_inc(v_typeName_518_);
lean_dec(v_cases_517_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_573_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
size_t v_sz_525_; size_t v___x_526_; lean_object* v___x_527_; 
v_sz_525_ = lean_array_size(v_alts_521_);
v___x_526_ = ((size_t)0ULL);
lean_inc_ref(v_alts_521_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_152_, v_w_153_, v_sz_525_, v___x_526_, v_alts_521_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_564_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_564_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_564_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_564_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___y_533_; uint8_t v___y_534_; lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___y_544_; size_t v___x_550_; size_t v___x_551_; uint8_t v___x_552_; 
v___x_540_ = l_Array_unzip___redArg(v_a_528_);
lean_dec(v_a_528_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_fst_541_);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
lean_inc(v_snd_542_);
lean_dec_ref(v___x_540_);
v___x_550_ = lean_ptr_addr(v_alts_521_);
lean_dec_ref(v_alts_521_);
v___x_551_ = lean_ptr_addr(v_fst_541_);
v___x_552_ = lean_usize_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_562_; 
v_isSharedCheck_562_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_563_);
v___x_554_ = v_c_154_;
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
else
{
lean_dec(v_c_154_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 3, v_fst_541_);
v___x_557_ = v___x_523_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_typeName_518_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_resultType_519_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_discr_520_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_fst_541_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
v___y_544_ = v___x_559_;
goto v___jp_543_;
}
}
}
}
else
{
lean_dec(v_fst_541_);
lean_del_object(v___x_523_);
lean_dec(v_discr_520_);
lean_dec_ref(v_resultType_519_);
lean_dec(v_typeName_518_);
v___y_544_ = v_c_154_;
goto v___jp_543_;
}
v___jp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_box(v___y_534_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_536_);
v___x_538_ = v___x_530_;
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
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_array_get_size(v_snd_542_);
v___x_547_ = lean_nat_dec_lt(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec(v_snd_542_);
v___y_533_ = v___y_544_;
v___y_534_ = v___x_547_;
goto v___jp_532_;
}
else
{
if (v___x_547_ == 0)
{
lean_dec(v_snd_542_);
v___y_533_ = v___y_544_;
v___y_534_ = v___x_547_;
goto v___jp_532_;
}
else
{
size_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_usize_of_nat(v___x_546_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__2(v_snd_542_, v___x_526_, v___x_548_);
lean_dec(v_snd_542_);
v___y_533_ = v___y_544_;
v___y_534_ = v___x_549_;
goto v___jp_532_;
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_523_);
lean_dec_ref(v_alts_521_);
lean_dec(v_discr_520_);
lean_dec_ref(v_resultType_519_);
lean_dec(v_typeName_518_);
lean_dec_ref_known(v_c_154_, 1);
v_a_565_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_527_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_527_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
case 5:
{
uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_w_153_);
v___x_574_ = 0;
v___x_575_ = lean_box(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_c_154_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
case 6:
{
uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_w_153_);
v___x_578_ = 0;
v___x_579_ = lean_box(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_c_154_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
case 8:
{
lean_object* v_k_582_; 
v_k_582_ = lean_ctor_get(v_c_154_, 3);
lean_inc_ref(v_k_582_);
v_k_168_ = v_k_582_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
case 9:
{
lean_object* v_k_583_; 
v_k_583_ = lean_ctor_get(v_c_154_, 5);
lean_inc_ref(v_k_583_);
v_k_168_ = v_k_583_;
v___y_169_ = v_a_155_;
v___y_170_ = v_a_156_;
v___y_171_ = v_a_157_;
v___y_172_ = v_a_158_;
v___y_173_ = v_a_159_;
goto v___jp_167_;
}
default: 
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec_ref(v_c_154_);
lean_dec(v_w_153_);
v___x_584_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__6);
v___x_585_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_584_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
return v___x_585_;
}
}
v___jp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_box(v___y_162_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
v___jp_167_:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_152_, v_w_153_, v_k_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
switch(lean_obj_tag(v_c_154_))
{
case 0:
{
lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v_decl_178_; lean_object* v_k_179_; size_t v___x_180_; size_t v___x_181_; uint8_t v___x_182_; 
v_fst_176_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_177_);
lean_dec(v_a_175_);
v_decl_178_ = lean_ctor_get(v_c_154_, 0);
v_k_179_ = lean_ctor_get(v_c_154_, 1);
v___x_180_ = lean_ptr_addr(v_k_179_);
v___x_181_ = lean_ptr_addr(v_fst_176_);
v___x_182_ = lean_usize_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
lean_inc_ref(v_decl_178_);
v_isSharedCheck_190_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_191_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_192_);
v___x_184_ = v_c_154_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_c_154_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_fst_176_);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_decl_178_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_fst_176_);
v___x_187_ = v_reuseFailAlloc_189_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
uint8_t v___x_188_; 
v___x_188_ = lean_unbox(v_snd_177_);
lean_dec(v_snd_177_);
v___y_162_ = v___x_188_;
v___y_163_ = v___x_187_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_193_; 
lean_dec(v_fst_176_);
v___x_193_ = lean_unbox(v_snd_177_);
lean_dec(v_snd_177_);
v___y_162_ = v___x_193_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 1:
{
lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v_decl_196_; lean_object* v_k_197_; size_t v___x_198_; size_t v___x_199_; uint8_t v___x_200_; 
v_fst_194_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_194_);
v_snd_195_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_195_);
lean_dec(v_a_175_);
v_decl_196_ = lean_ctor_get(v_c_154_, 0);
v_k_197_ = lean_ctor_get(v_c_154_, 1);
v___x_198_ = lean_ptr_addr(v_k_197_);
v___x_199_ = lean_ptr_addr(v_fst_194_);
v___x_200_ = lean_usize_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
lean_inc_ref(v_decl_196_);
v_isSharedCheck_208_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_209_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_210_);
v___x_202_ = v_c_154_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_c_154_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_fst_194_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_decl_196_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_fst_194_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
uint8_t v___x_206_; 
v___x_206_ = lean_unbox(v_snd_195_);
lean_dec(v_snd_195_);
v___y_162_ = v___x_206_;
v___y_163_ = v___x_205_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_211_; 
lean_dec(v_fst_194_);
v___x_211_ = lean_unbox(v_snd_195_);
lean_dec(v_snd_195_);
v___y_162_ = v___x_211_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 2:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v_decl_214_; lean_object* v_k_215_; size_t v___x_216_; size_t v___x_217_; uint8_t v___x_218_; 
v_fst_212_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_212_);
v_snd_213_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_213_);
lean_dec(v_a_175_);
v_decl_214_ = lean_ctor_get(v_c_154_, 0);
v_k_215_ = lean_ctor_get(v_c_154_, 1);
v___x_216_ = lean_ptr_addr(v_k_215_);
v___x_217_ = lean_ptr_addr(v_fst_212_);
v___x_218_ = lean_usize_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
lean_inc_ref(v_decl_214_);
v_isSharedCheck_226_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; 
v_unused_227_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_228_);
v___x_220_ = v_c_154_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_c_154_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v_fst_212_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_decl_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_fst_212_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_snd_213_);
lean_dec(v_snd_213_);
v___y_162_ = v___x_224_;
v___y_163_ = v___x_223_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_229_; 
lean_dec(v_fst_212_);
v___x_229_ = lean_unbox(v_snd_213_);
lean_dec(v_snd_213_);
v___y_162_ = v___x_229_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 7:
{
lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v_fvarId_232_; lean_object* v_i_233_; lean_object* v_y_234_; lean_object* v_k_235_; size_t v___x_236_; size_t v___x_237_; uint8_t v___x_238_; 
v_fst_230_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_230_);
v_snd_231_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_231_);
lean_dec(v_a_175_);
v_fvarId_232_ = lean_ctor_get(v_c_154_, 0);
v_i_233_ = lean_ctor_get(v_c_154_, 1);
v_y_234_ = lean_ctor_get(v_c_154_, 2);
v_k_235_ = lean_ctor_get(v_c_154_, 3);
v___x_236_ = lean_ptr_addr(v_k_235_);
v___x_237_ = lean_ptr_addr(v_fst_230_);
v___x_238_ = lean_usize_dec_eq(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
lean_inc(v_y_234_);
lean_inc(v_i_233_);
lean_inc(v_fvarId_232_);
v_isSharedCheck_246_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; lean_object* v_unused_250_; 
v_unused_247_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_250_);
v___x_240_ = v_c_154_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_c_154_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 3, v_fst_230_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_fvarId_232_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_i_233_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_y_234_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_fst_230_);
v___x_243_ = v_reuseFailAlloc_245_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_snd_231_);
lean_dec(v_snd_231_);
v___y_162_ = v___x_244_;
v___y_163_ = v___x_243_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_251_; 
lean_dec(v_fst_230_);
v___x_251_ = lean_unbox(v_snd_231_);
lean_dec(v_snd_231_);
v___y_162_ = v___x_251_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 9:
{
lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v_fvarId_254_; lean_object* v_i_255_; lean_object* v_offset_256_; lean_object* v_y_257_; lean_object* v_ty_258_; lean_object* v_k_259_; size_t v___x_260_; size_t v___x_261_; uint8_t v___x_262_; 
v_fst_252_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_252_);
v_snd_253_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_253_);
lean_dec(v_a_175_);
v_fvarId_254_ = lean_ctor_get(v_c_154_, 0);
v_i_255_ = lean_ctor_get(v_c_154_, 1);
v_offset_256_ = lean_ctor_get(v_c_154_, 2);
v_y_257_ = lean_ctor_get(v_c_154_, 3);
v_ty_258_ = lean_ctor_get(v_c_154_, 4);
v_k_259_ = lean_ctor_get(v_c_154_, 5);
v___x_260_ = lean_ptr_addr(v_k_259_);
v___x_261_ = lean_ptr_addr(v_fst_252_);
v___x_262_ = lean_usize_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
lean_inc_ref(v_ty_258_);
lean_inc(v_y_257_);
lean_inc(v_offset_256_);
lean_inc(v_i_255_);
lean_inc(v_fvarId_254_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; lean_object* v_unused_274_; lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_271_ = lean_ctor_get(v_c_154_, 5);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_c_154_, 4);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_273_);
v_unused_274_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_274_);
v_unused_275_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_276_);
v___x_264_ = v_c_154_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_c_154_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 5, v_fst_252_);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_fvarId_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_i_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_offset_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_y_257_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_ty_258_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_fst_252_);
v___x_267_ = v_reuseFailAlloc_269_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_snd_253_);
lean_dec(v_snd_253_);
v___y_162_ = v___x_268_;
v___y_163_ = v___x_267_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_277_; 
lean_dec(v_fst_252_);
v___x_277_ = lean_unbox(v_snd_253_);
lean_dec(v_snd_253_);
v___y_162_ = v___x_277_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 8:
{
lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v_fvarId_280_; lean_object* v_i_281_; lean_object* v_y_282_; lean_object* v_k_283_; size_t v___x_284_; size_t v___x_285_; uint8_t v___x_286_; 
v_fst_278_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_278_);
v_snd_279_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_279_);
lean_dec(v_a_175_);
v_fvarId_280_ = lean_ctor_get(v_c_154_, 0);
v_i_281_ = lean_ctor_get(v_c_154_, 1);
v_y_282_ = lean_ctor_get(v_c_154_, 2);
v_k_283_ = lean_ctor_get(v_c_154_, 3);
v___x_284_ = lean_ptr_addr(v_k_283_);
v___x_285_ = lean_ptr_addr(v_fst_278_);
v___x_286_ = lean_usize_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
lean_inc(v_y_282_);
lean_inc(v_i_281_);
lean_inc(v_fvarId_280_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_295_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_298_);
v___x_288_ = v_c_154_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_c_154_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 3, v_fst_278_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_fvarId_280_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_i_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_y_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_fst_278_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
uint8_t v___x_292_; 
v___x_292_ = lean_unbox(v_snd_279_);
lean_dec(v_snd_279_);
v___y_162_ = v___x_292_;
v___y_163_ = v___x_291_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_299_; 
lean_dec(v_fst_278_);
v___x_299_ = lean_unbox(v_snd_279_);
lean_dec(v_snd_279_);
v___y_162_ = v___x_299_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 10:
{
lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v_fvarId_302_; lean_object* v_cidx_303_; lean_object* v_k_304_; size_t v___x_305_; size_t v___x_306_; uint8_t v___x_307_; 
v_fst_300_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_300_);
v_snd_301_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_301_);
lean_dec(v_a_175_);
v_fvarId_302_ = lean_ctor_get(v_c_154_, 0);
v_cidx_303_ = lean_ctor_get(v_c_154_, 1);
v_k_304_ = lean_ctor_get(v_c_154_, 2);
v___x_305_ = lean_ptr_addr(v_k_304_);
v___x_306_ = lean_ptr_addr(v_fst_300_);
v___x_307_ = lean_usize_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
lean_inc(v_cidx_303_);
lean_inc(v_fvarId_302_);
v_isSharedCheck_315_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_316_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_318_);
v___x_309_ = v_c_154_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_dec(v_c_154_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 2, v_fst_300_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_fvarId_302_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_cidx_303_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_fst_300_);
v___x_312_ = v_reuseFailAlloc_314_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
uint8_t v___x_313_; 
v___x_313_ = lean_unbox(v_snd_301_);
lean_dec(v_snd_301_);
v___y_162_ = v___x_313_;
v___y_163_ = v___x_312_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_319_; 
lean_dec(v_fst_300_);
v___x_319_ = lean_unbox(v_snd_301_);
lean_dec(v_snd_301_);
v___y_162_ = v___x_319_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 11:
{
lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v_fvarId_322_; lean_object* v_n_323_; uint8_t v_check_324_; uint8_t v_persistent_325_; lean_object* v_k_326_; size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v_fst_320_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_321_);
lean_dec(v_a_175_);
v_fvarId_322_ = lean_ctor_get(v_c_154_, 0);
v_n_323_ = lean_ctor_get(v_c_154_, 1);
v_check_324_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*3);
v_persistent_325_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*3 + 1);
v_k_326_ = lean_ctor_get(v_c_154_, 2);
v___x_327_ = lean_ptr_addr(v_k_326_);
v___x_328_ = lean_ptr_addr(v_fst_320_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
lean_inc(v_n_323_);
lean_inc(v_fvarId_322_);
v_isSharedCheck_337_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_338_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_340_);
v___x_331_ = v_c_154_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_c_154_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 2, v_fst_320_);
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_fvarId_322_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_n_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_fst_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*3, v_check_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*3 + 1, v_persistent_325_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
uint8_t v___x_335_; 
v___x_335_ = lean_unbox(v_snd_321_);
lean_dec(v_snd_321_);
v___y_162_ = v___x_335_;
v___y_163_ = v___x_334_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_341_; 
lean_dec(v_fst_320_);
v___x_341_ = lean_unbox(v_snd_321_);
lean_dec(v_snd_321_);
v___y_162_ = v___x_341_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 12:
{
lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v_fvarId_344_; lean_object* v_n_345_; uint8_t v_check_346_; uint8_t v_persistent_347_; lean_object* v_objs_x3f_348_; lean_object* v_k_349_; size_t v___x_350_; size_t v___x_351_; uint8_t v___x_352_; 
v_fst_342_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_342_);
v_snd_343_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_343_);
lean_dec(v_a_175_);
v_fvarId_344_ = lean_ctor_get(v_c_154_, 0);
v_n_345_ = lean_ctor_get(v_c_154_, 1);
v_check_346_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*4);
v_persistent_347_ = lean_ctor_get_uint8(v_c_154_, sizeof(void*)*4 + 1);
v_objs_x3f_348_ = lean_ctor_get(v_c_154_, 2);
v_k_349_ = lean_ctor_get(v_c_154_, 3);
v___x_350_ = lean_ptr_addr(v_k_349_);
v___x_351_ = lean_ptr_addr(v_fst_342_);
v___x_352_ = lean_usize_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
lean_inc(v_objs_x3f_348_);
lean_inc(v_n_345_);
lean_inc(v_fvarId_344_);
v_isSharedCheck_360_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_361_ = lean_ctor_get(v_c_154_, 3);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_c_154_, 2);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_364_);
v___x_354_ = v_c_154_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_c_154_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 3, v_fst_342_);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_fvarId_344_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_n_345_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_objs_x3f_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_fst_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*4, v_check_346_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*4 + 1, v_persistent_347_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
uint8_t v___x_358_; 
v___x_358_ = lean_unbox(v_snd_343_);
lean_dec(v_snd_343_);
v___y_162_ = v___x_358_;
v___y_163_ = v___x_357_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_365_; 
lean_dec(v_fst_342_);
v___x_365_ = lean_unbox(v_snd_343_);
lean_dec(v_snd_343_);
v___y_162_ = v___x_365_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
case 13:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v_fvarId_368_; lean_object* v_k_369_; size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v_fst_366_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_367_);
lean_dec(v_a_175_);
v_fvarId_368_ = lean_ctor_get(v_c_154_, 0);
v_k_369_ = lean_ctor_get(v_c_154_, 1);
v___x_370_ = lean_ptr_addr(v_k_369_);
v___x_371_ = lean_ptr_addr(v_fst_366_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
lean_inc(v_fvarId_368_);
v_isSharedCheck_380_ = !lean_is_exclusive(v_c_154_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_381_ = lean_ctor_get(v_c_154_, 1);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_c_154_, 0);
lean_dec(v_unused_382_);
v___x_374_ = v_c_154_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_c_154_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v_fst_366_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_fvarId_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_fst_366_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
uint8_t v___x_378_; 
v___x_378_ = lean_unbox(v_snd_367_);
lean_dec(v_snd_367_);
v___y_162_ = v___x_378_;
v___y_163_ = v___x_377_;
goto v___jp_161_;
}
}
}
else
{
uint8_t v___x_383_; 
lean_dec(v_fst_366_);
v___x_383_ = lean_unbox(v_snd_367_);
lean_dec(v_snd_367_);
v___y_162_ = v___x_383_;
v___y_163_ = v_c_154_;
goto v___jp_161_;
}
}
default: 
{
lean_object* v_snd_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
lean_dec_ref(v_c_154_);
v_snd_384_ = lean_ctor_get(v_a_175_, 1);
lean_inc(v_snd_384_);
lean_dec(v_a_175_);
v___x_385_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__3);
v___x_386_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0(v___x_385_);
v___x_387_ = lean_unbox(v_snd_384_);
lean_dec(v_snd_384_);
v___y_162_ = v___x_387_;
v___y_163_ = v___x_386_;
goto v___jp_161_;
}
}
}
else
{
lean_dec_ref(v_c_154_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(lean_object* v_info_586_, lean_object* v_w_587_, size_t v_sz_588_, size_t v_i_589_, lean_object* v_bs_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_lt(v_i_589_, v_sz_588_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v_w_587_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v_bs_590_);
return v___x_598_;
}
else
{
lean_object* v_v_599_; lean_object* v___x_600_; lean_object* v_bs_x27_601_; lean_object* v___y_603_; 
v_v_599_ = lean_array_uget(v_bs_590_, v_i_589_);
v___x_600_ = lean_unsigned_to_nat(0u);
v_bs_x27_601_ = lean_array_uset(v_bs_590_, v_i_589_, v___x_600_);
switch(lean_obj_tag(v_v_599_))
{
case 0:
{
lean_object* v_code_628_; 
v_code_628_ = lean_ctor_get(v_v_599_, 2);
lean_inc_ref(v_code_628_);
v___y_603_ = v_code_628_;
goto v___jp_602_;
}
case 1:
{
lean_object* v_code_629_; 
v_code_629_ = lean_ctor_get(v_v_599_, 1);
lean_inc_ref(v_code_629_);
v___y_603_ = v_code_629_;
goto v___jp_602_;
}
default: 
{
lean_object* v_code_630_; 
v_code_630_ = lean_ctor_get(v_v_599_, 0);
lean_inc_ref(v_code_630_);
v___y_603_ = v_code_630_;
goto v___jp_602_;
}
}
v___jp_602_:
{
lean_object* v___x_604_; 
lean_inc(v_w_587_);
v___x_604_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_586_, v_w_587_, v___y_603_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_619_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_fst_606_ = lean_ctor_get(v_a_605_, 0);
v_snd_607_ = lean_ctor_get(v_a_605_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_619_ == 0)
{
v___x_609_ = v_a_605_;
v_isShared_610_ = v_isSharedCheck_619_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
lean_dec(v_a_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_619_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_599_, v_fst_606_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_607_);
v___x_613_ = v_reuseFailAlloc_618_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_589_, v___x_614_);
v___x_616_ = lean_array_uset(v_bs_x27_601_, v_i_589_, v___x_613_);
v_i_589_ = v___x_615_;
v_bs_590_ = v___x_616_;
goto _start;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_bs_x27_601_);
lean_dec(v_v_599_);
lean_dec(v_w_587_);
v_a_620_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_604_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_604_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1___boxed(lean_object* v_info_631_, lean_object* v_w_632_, lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_bs_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_643_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__1(v_info_631_, v_w_632_, v_sz_boxed_642_, v_i_boxed_643_, v_bs_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v_info_631_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___boxed(lean_object* v_info_645_, lean_object* v_w_646_, lean_object* v_c_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_645_, v_w_646_, v_c_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec_ref(v_info_645_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v_ngen_658_; lean_object* v_namePrefix_659_; lean_object* v_idx_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_689_; 
v___x_657_ = lean_st_ref_get(v___y_655_);
v_ngen_658_ = lean_ctor_get(v___x_657_, 2);
lean_inc_ref(v_ngen_658_);
lean_dec(v___x_657_);
v_namePrefix_659_ = lean_ctor_get(v_ngen_658_, 0);
v_idx_660_ = lean_ctor_get(v_ngen_658_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_ngen_658_);
if (v_isSharedCheck_689_ == 0)
{
v___x_662_ = v_ngen_658_;
v_isShared_663_ = v_isSharedCheck_689_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_idx_660_);
lean_inc(v_namePrefix_659_);
lean_dec(v_ngen_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_689_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v_env_665_; lean_object* v_nextMacroScope_666_; lean_object* v_auxDeclNGen_667_; lean_object* v_traceState_668_; lean_object* v_cache_669_; lean_object* v_messages_670_; lean_object* v_infoState_671_; lean_object* v_snapshotTasks_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_687_; 
v___x_664_ = lean_st_ref_take(v___y_655_);
v_env_665_ = lean_ctor_get(v___x_664_, 0);
v_nextMacroScope_666_ = lean_ctor_get(v___x_664_, 1);
v_auxDeclNGen_667_ = lean_ctor_get(v___x_664_, 3);
v_traceState_668_ = lean_ctor_get(v___x_664_, 4);
v_cache_669_ = lean_ctor_get(v___x_664_, 5);
v_messages_670_ = lean_ctor_get(v___x_664_, 6);
v_infoState_671_ = lean_ctor_get(v___x_664_, 7);
v_snapshotTasks_672_ = lean_ctor_get(v___x_664_, 8);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_664_, 2);
lean_dec(v_unused_688_);
v___x_674_ = v___x_664_;
v_isShared_675_ = v_isSharedCheck_687_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snapshotTasks_672_);
lean_inc(v_infoState_671_);
lean_inc(v_messages_670_);
lean_inc(v_cache_669_);
lean_inc(v_traceState_668_);
lean_inc(v_auxDeclNGen_667_);
lean_inc(v_nextMacroScope_666_);
lean_inc(v_env_665_);
lean_dec(v___x_664_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_687_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_r_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_inc(v_idx_660_);
lean_inc(v_namePrefix_659_);
v_r_676_ = l_Lean_Name_num___override(v_namePrefix_659_, v_idx_660_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_idx_660_, v___x_677_);
lean_dec(v_idx_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_678_);
v___x_680_ = v___x_662_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_namePrefix_659_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_686_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 2, v___x_680_);
v___x_682_ = v___x_674_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_env_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_nextMacroScope_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_auxDeclNGen_667_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_traceState_668_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v_cache_669_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v_messages_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_infoState_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_snapshotTasks_672_);
v___x_682_ = v_reuseFailAlloc_685_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_st_ref_set(v___y_655_, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_r_676_);
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg___boxed(lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_690_);
lean_dec(v___y_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v___x_699_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_697_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0___boxed(lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_714_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(0);
v___x_722_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__3));
v___x_723_ = l_Lean_Expr_const___override(v___x_722_, v___x_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(lean_object* v_x_724_, lean_object* v_info_725_, lean_object* v_c_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0(v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_a_734_, 2);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go(v_info_725_, v_a_734_, v_c_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_790_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_790_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_790_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_790_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_snd_740_; uint8_t v___x_741_; 
v_snd_740_ = lean_ctor_get(v_a_736_, 1);
v___x_741_ = lean_unbox(v_snd_740_);
if (v___x_741_ == 0)
{
lean_object* v_fst_742_; lean_object* v___x_744_; 
lean_dec(v_a_734_);
lean_dec(v_x_724_);
v_fst_742_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_742_);
lean_dec(v_a_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_fst_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v_fst_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_788_; 
lean_del_object(v___x_738_);
v_fst_746_ = lean_ctor_get(v_a_736_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_736_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_a_736_, 1);
lean_dec(v_unused_789_);
v___x_748_ = v_a_736_;
v_isShared_749_ = v_isSharedCheck_788_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_fst_746_);
lean_dec(v_a_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_788_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__1));
v___x_751_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_750_, v_a_729_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_779_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_779_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_779_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_779_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_size_756_; lean_object* v___x_757_; lean_object* v_lctx_758_; lean_object* v_nextIdx_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_778_; 
v_size_756_ = lean_ctor_get(v_info_725_, 2);
v___x_757_ = lean_st_ref_take(v_a_729_);
v_lctx_758_ = lean_ctor_get(v___x_757_, 0);
v_nextIdx_759_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_778_ == 0)
{
v___x_761_ = v___x_757_;
v_isShared_762_ = v_isSharedCheck_778_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_nextIdx_759_);
lean_inc(v_lctx_758_);
lean_dec(v___x_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_778_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
uint8_t v___x_763_; lean_object* v___x_765_; 
v___x_763_ = 1;
lean_inc(v_size_756_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 11);
lean_ctor_set(v___x_748_, 1, v_x_724_);
lean_ctor_set(v___x_748_, 0, v_size_756_);
v___x_765_ = v___x_748_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_size_756_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_x_724_);
v___x_765_ = v_reuseFailAlloc_777_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_766_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___closed__4);
v___x_767_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_767_, 0, v_a_734_);
lean_ctor_set(v___x_767_, 1, v_a_752_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
lean_ctor_set(v___x_767_, 3, v___x_765_);
lean_inc_ref(v___x_767_);
v___x_768_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_763_, v_lctx_758_, v___x_767_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_768_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_nextIdx_759_);
v___x_770_ = v_reuseFailAlloc_776_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = lean_st_ref_set(v_a_729_, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_767_);
lean_ctor_set(v___x_772_, 1, v_fst_746_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_772_);
v___x_774_ = v___x_754_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_del_object(v___x_748_);
lean_dec(v_fst_746_);
lean_dec(v_a_734_);
lean_dec(v_x_724_);
v_a_780_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_751_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_751_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_734_);
lean_dec(v_x_724_);
v_a_791_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_735_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_735_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_c_726_);
lean_dec(v_x_724_);
v_a_799_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_733_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_733_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S___boxed(lean_object* v_x_807_, lean_object* v_info_808_, lean_object* v_c_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_807_, v_info_808_, v_c_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_info_808_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___redArg(v___y_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0___boxed(lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_spec__0_spec__0(v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(lean_object* v_x_831_, lean_object* v_as_832_, size_t v_i_833_, size_t v_stop_834_){
_start:
{
uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_eq(v_i_833_, v_stop_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_836_ = lean_array_uget_borrowed(v_as_832_, v_i_833_);
v___x_837_ = 1;
lean_inc(v_x_831_);
v___x_838_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_831_);
v___x_839_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v___x_837_, v___x_836_, v___x_838_);
lean_dec(v___x_838_);
if (v___x_839_ == 0)
{
size_t v___x_840_; size_t v___x_841_; 
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_833_, v___x_840_);
v_i_833_ = v___x_841_;
goto _start;
}
else
{
lean_dec(v_x_831_);
return v___x_839_;
}
}
else
{
uint8_t v___x_843_; 
lean_dec(v_x_831_);
v___x_843_ = 0;
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0___boxed(lean_object* v_x_844_, lean_object* v_as_845_, lean_object* v_i_846_, lean_object* v_stop_847_){
_start:
{
size_t v_i_boxed_848_; size_t v_stop_boxed_849_; uint8_t v_res_850_; lean_object* v_r_851_; 
v_i_boxed_848_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_stop_boxed_849_ = lean_unbox_usize(v_stop_847_);
lean_dec(v_stop_847_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_844_, v_as_845_, v_i_boxed_848_, v_stop_boxed_849_);
lean_dec_ref(v_as_845_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(lean_object* v_instr_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_instr_852_) == 0)
{
lean_object* v_decl_854_; lean_object* v_value_855_; 
v_decl_854_ = lean_ctor_get(v_instr_852_, 0);
v_value_855_ = lean_ctor_get(v_decl_854_, 3);
if (lean_obj_tag(v_value_855_) == 5)
{
lean_object* v_args_856_; lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_args_856_ = lean_ctor_get(v_value_855_, 1);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_array_get_size(v_args_856_);
v___x_859_ = lean_nat_dec_lt(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_dec(v_x_853_);
return v___x_859_;
}
else
{
if (v___x_859_ == 0)
{
lean_dec(v_x_853_);
return v___x_859_;
}
else
{
size_t v___x_860_; size_t v___x_861_; uint8_t v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_858_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing_spec__0(v_x_853_, v_args_856_, v___x_860_, v___x_861_);
return v___x_862_;
}
}
}
else
{
uint8_t v___x_863_; 
lean_dec(v_x_853_);
v___x_863_ = 0;
return v___x_863_;
}
}
else
{
uint8_t v___x_864_; 
lean_dec(v_x_853_);
v___x_864_ = 0;
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing___boxed(lean_object* v_instr_865_, lean_object* v_x_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_865_, v_x_866_);
lean_dec_ref(v_instr_865_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(uint8_t v_x_869_){
_start:
{
switch(v_x_869_)
{
case 0:
{
lean_object* v___x_870_; 
v___x_870_ = lean_unsigned_to_nat(0u);
return v___x_870_;
}
case 1:
{
lean_object* v___x_871_; 
v___x_871_ = lean_unsigned_to_nat(1u);
return v___x_871_;
}
default: 
{
lean_object* v___x_872_; 
v___x_872_ = lean_unsigned_to_nat(2u);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx___boxed(lean_object* v_x_873_){
_start:
{
uint8_t v_x_boxed_874_; lean_object* v_res_875_; 
v_x_boxed_874_ = lean_unbox(v_x_873_);
v_res_875_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_boxed_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(uint8_t v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorIdx(v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx___boxed(lean_object* v_x_878_){
_start:
{
uint8_t v_x_4__boxed_879_; lean_object* v_res_880_; 
v_x_4__boxed_879_ = lean_unbox(v_x_878_);
v_res_880_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_toCtorIdx(v_x_4__boxed_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(lean_object* v_k_881_){
_start:
{
lean_inc(v_k_881_);
return v_k_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg___boxed(lean_object* v_k_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___redArg(v_k_882_);
lean_dec(v_k_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(lean_object* v_motive_884_, lean_object* v_ctorIdx_885_, uint8_t v_t_886_, lean_object* v_h_887_, lean_object* v_k_888_){
_start:
{
lean_inc(v_k_888_);
return v_k_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim___boxed(lean_object* v_motive_889_, lean_object* v_ctorIdx_890_, lean_object* v_t_891_, lean_object* v_h_892_, lean_object* v_k_893_){
_start:
{
uint8_t v_t_boxed_894_; lean_object* v_res_895_; 
v_t_boxed_894_ = lean_unbox(v_t_891_);
v_res_895_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ctorElim(v_motive_889_, v_ctorIdx_890_, v_t_boxed_894_, v_h_892_, v_k_893_);
lean_dec(v_k_893_);
lean_dec(v_ctorIdx_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(lean_object* v_ownedArg_896_){
_start:
{
lean_inc(v_ownedArg_896_);
return v_ownedArg_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg___boxed(lean_object* v_ownedArg_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___redArg(v_ownedArg_897_);
lean_dec(v_ownedArg_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(lean_object* v_motive_899_, uint8_t v_t_900_, lean_object* v_h_901_, lean_object* v_ownedArg_902_){
_start:
{
lean_inc(v_ownedArg_902_);
return v_ownedArg_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim___boxed(lean_object* v_motive_903_, lean_object* v_t_904_, lean_object* v_h_905_, lean_object* v_ownedArg_906_){
_start:
{
uint8_t v_t_boxed_907_; lean_object* v_res_908_; 
v_t_boxed_907_ = lean_unbox(v_t_904_);
v_res_908_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_ownedArg_elim(v_motive_903_, v_t_boxed_907_, v_h_905_, v_ownedArg_906_);
lean_dec(v_ownedArg_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(lean_object* v_other_909_){
_start:
{
lean_inc(v_other_909_);
return v_other_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg___boxed(lean_object* v_other_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___redArg(v_other_910_);
lean_dec(v_other_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(lean_object* v_motive_912_, uint8_t v_t_913_, lean_object* v_h_914_, lean_object* v_other_915_){
_start:
{
lean_inc(v_other_915_);
return v_other_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim___boxed(lean_object* v_motive_916_, lean_object* v_t_917_, lean_object* v_h_918_, lean_object* v_other_919_){
_start:
{
uint8_t v_t_boxed_920_; lean_object* v_res_921_; 
v_t_boxed_920_ = lean_unbox(v_t_917_);
v_res_921_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_other_elim(v_motive_916_, v_t_boxed_920_, v_h_918_, v_other_919_);
lean_dec(v_other_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(lean_object* v_none_922_){
_start:
{
lean_inc(v_none_922_);
return v_none_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg___boxed(lean_object* v_none_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___redArg(v_none_923_);
lean_dec(v_none_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(lean_object* v_motive_925_, uint8_t v_t_926_, lean_object* v_h_927_, lean_object* v_none_928_){
_start:
{
lean_inc(v_none_928_);
return v_none_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim___boxed(lean_object* v_motive_929_, lean_object* v_t_930_, lean_object* v_h_931_, lean_object* v_none_932_){
_start:
{
uint8_t v_t_boxed_933_; lean_object* v_res_934_; 
v_t_boxed_933_ = lean_unbox(v_t_930_);
v_res_934_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_UseClassification_none_elim(v_motive_929_, v_t_boxed_933_, v_h_931_, v_none_932_);
lean_dec(v_none_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(lean_object* v_x_935_, lean_object* v_as_936_, size_t v_sz_937_, size_t v_i_938_, lean_object* v_b_939_){
_start:
{
lean_object* v_a_942_; uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_938_, v_sz_937_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_939_);
return v___x_947_;
}
else
{
lean_object* v_snd_948_; lean_object* v_fst_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_993_; 
v_snd_948_ = lean_ctor_get(v_b_939_, 1);
v_fst_949_ = lean_ctor_get(v_b_939_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_b_939_);
if (v_isSharedCheck_993_ == 0)
{
v___x_951_ = v_b_939_;
v_isShared_952_ = v_isSharedCheck_993_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_snd_948_);
lean_inc(v_fst_949_);
lean_dec(v_b_939_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_993_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_array_953_; lean_object* v_start_954_; lean_object* v_stop_955_; uint8_t v___x_956_; 
v_array_953_ = lean_ctor_get(v_snd_948_, 0);
v_start_954_ = lean_ctor_get(v_snd_948_, 1);
v_stop_955_ = lean_ctor_get(v_snd_948_, 2);
v___x_956_ = lean_nat_dec_lt(v_start_954_, v_stop_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_958_; 
if (v_isShared_952_ == 0)
{
v___x_958_ = v___x_951_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_fst_949_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_948_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
else
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_989_; 
lean_inc(v_stop_955_);
lean_inc(v_start_954_);
lean_inc_ref(v_array_953_);
v_isSharedCheck_989_ = !lean_is_exclusive(v_snd_948_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; 
v_unused_990_ = lean_ctor_get(v_snd_948_, 2);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_snd_948_, 1);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_snd_948_, 0);
lean_dec(v_unused_992_);
v___x_962_ = v_snd_948_;
v_isShared_963_ = v_isSharedCheck_989_;
goto v_resetjp_961_;
}
else
{
lean_dec(v_snd_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_989_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v_a_964_ = lean_array_uget_borrowed(v_as_936_, v_i_938_);
v___x_965_ = lean_array_fget(v_array_953_, v_start_954_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_start_954_, v___x_966_);
lean_dec(v_start_954_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_967_);
v___x_969_ = v___x_962_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_array_953_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_stop_955_);
v___x_969_ = v_reuseFailAlloc_988_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
uint8_t v___y_971_; 
if (lean_obj_tag(v_a_964_) == 1)
{
lean_object* v_fvarId_976_; uint8_t v___x_977_; 
v_fvarId_976_ = lean_ctor_get(v_a_964_, 0);
v___x_977_ = l_Lean_instBEqFVarId_beq(v_fvarId_976_, v_x_935_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_dec(v___x_965_);
lean_del_object(v___x_951_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v_fst_949_);
lean_ctor_set(v___x_978_, 1, v___x_969_);
v_a_942_ = v___x_978_;
goto v___jp_941_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = lean_unbox(v_fst_949_);
switch(v___x_979_)
{
case 0:
{
uint8_t v_borrow_980_; 
v_borrow_980_ = lean_ctor_get_uint8(v___x_965_, sizeof(void*)*3);
lean_dec(v___x_965_);
if (v_borrow_980_ == 0)
{
uint8_t v___x_981_; 
v___x_981_ = lean_unbox(v_fst_949_);
lean_dec(v_fst_949_);
v___y_971_ = v___x_981_;
goto v___jp_970_;
}
else
{
uint8_t v___x_982_; 
lean_dec(v_fst_949_);
v___x_982_ = 1;
v___y_971_ = v___x_982_;
goto v___jp_970_;
}
}
case 1:
{
uint8_t v___x_983_; 
lean_dec(v___x_965_);
v___x_983_ = lean_unbox(v_fst_949_);
lean_dec(v_fst_949_);
v___y_971_ = v___x_983_;
goto v___jp_970_;
}
default: 
{
uint8_t v_borrow_984_; 
lean_dec(v_fst_949_);
v_borrow_984_ = lean_ctor_get_uint8(v___x_965_, sizeof(void*)*3);
lean_dec(v___x_965_);
if (v_borrow_984_ == 0)
{
uint8_t v___x_985_; 
v___x_985_ = 0;
v___y_971_ = v___x_985_;
goto v___jp_970_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = 1;
v___y_971_ = v___x_986_;
goto v___jp_970_;
}
}
}
}
}
else
{
lean_object* v___x_987_; 
lean_dec(v___x_965_);
lean_del_object(v___x_951_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_fst_949_);
lean_ctor_set(v___x_987_, 1, v___x_969_);
v_a_942_ = v___x_987_;
goto v___jp_941_;
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_box(v___y_971_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_969_);
lean_ctor_set(v___x_951_, 0, v___x_972_);
v___x_974_ = v___x_951_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
v_a_942_ = v___x_974_;
goto v___jp_941_;
}
}
}
}
}
}
}
v___jp_941_:
{
size_t v___x_943_; size_t v___x_944_; 
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_938_, v___x_943_);
v_i_938_ = v___x_944_;
v_b_939_ = v_a_942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg___boxed(lean_object* v_x_994_, lean_object* v_as_995_, lean_object* v_sz_996_, lean_object* v_i_997_, lean_object* v_b_998_, lean_object* v___y_999_){
_start:
{
size_t v_sz_boxed_1000_; size_t v_i_boxed_1001_; lean_object* v_res_1002_; 
v_sz_boxed_1000_ = lean_unbox_usize(v_sz_996_);
lean_dec(v_sz_996_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_994_, v_as_995_, v_sz_boxed_1000_, v_i_boxed_1001_, v_b_998_);
lean_dec_ref(v_as_995_);
lean_dec(v_x_994_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(lean_object* v_instr_1003_, lean_object* v_x_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
if (lean_obj_tag(v_instr_1003_) == 0)
{
lean_object* v_decl_1021_; lean_object* v_value_1022_; 
v_decl_1021_ = lean_ctor_get(v_instr_1003_, 0);
v_value_1022_ = lean_ctor_get(v_decl_1021_, 3);
lean_inc(v_value_1022_);
switch(lean_obj_tag(v_value_1022_))
{
case 9:
{
lean_object* v_fn_1023_; lean_object* v_args_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref_known(v_instr_1003_, 1);
v_fn_1023_ = lean_ctor_get(v_value_1022_, 0);
v_args_1024_ = lean_ctor_get(v_value_1022_, 1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_value_1022_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1026_ = v_value_1022_;
v_isShared_1027_ = v_isSharedCheck_1086_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_args_1024_);
lean_inc(v_fn_1023_);
lean_dec(v_value_1022_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1086_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
lean_inc_ref(v_args_1024_);
lean_inc(v_fn_1023_);
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fn_1023_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_args_1024_);
v___x_1029_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_fn_1023_, v_a_1009_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1076_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1076_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1076_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
if (lean_obj_tag(v_a_1031_) == 1)
{
lean_object* v_val_1035_; lean_object* v_params_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; size_t v_sz_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
lean_del_object(v___x_1033_);
lean_dec_ref(v___x_1029_);
v_val_1035_ = lean_ctor_get(v_a_1031_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_a_1031_, 1);
v_params_1036_ = lean_ctor_get(v_val_1035_, 3);
lean_inc_ref(v_params_1036_);
lean_dec(v_val_1035_);
v___x_1037_ = 2;
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = lean_array_get_size(v_params_1036_);
v___x_1040_ = l_Array_toSubarray___redArg(v_params_1036_, v___x_1038_, v___x_1039_);
v___x_1041_ = lean_box(v___x_1037_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_1040_);
v_sz_1043_ = lean_array_size(v_args_1024_);
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1004_, v_args_1024_, v_sz_1043_, v___x_1044_, v___x_1042_);
lean_dec_ref(v_args_1024_);
lean_dec(v_x_1004_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_fst_1050_; lean_object* v___x_1052_; 
v_fst_1050_ = lean_ctor_get(v_a_1046_, 0);
lean_inc(v_fst_1050_);
lean_dec(v_a_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_fst_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_fst_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1045_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1045_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
uint8_t v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
lean_dec(v_a_1031_);
lean_dec_ref(v_args_1024_);
v___x_1063_ = 1;
v___x_1064_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1004_);
v___x_1065_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1063_, v___x_1029_, v___x_1064_);
lean_dec(v___x_1064_);
lean_dec_ref(v___x_1029_);
if (v___x_1065_ == 0)
{
uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1066_ = 2;
v___x_1067_ = lean_box(v___x_1066_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1067_);
v___x_1069_ = v___x_1033_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = 0;
v___x_1072_ = lean_box(v___x_1071_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1072_);
v___x_1074_ = v___x_1033_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_args_1024_);
lean_dec(v_x_1004_);
v_a_1077_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1030_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1030_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
case 10:
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1112_; 
v_isSharedCheck_1112_ = !lean_is_exclusive(v_instr_1003_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v_instr_1003_, 0);
lean_dec(v_unused_1113_);
v___x_1088_ = v_instr_1003_;
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v_instr_1003_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_fn_1090_; lean_object* v_args_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1111_; 
v_fn_1090_ = lean_ctor_get(v_value_1022_, 0);
v_args_1091_ = lean_ctor_get(v_value_1022_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_value_1022_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1093_ = v_value_1022_;
v_isShared_1094_ = v_isSharedCheck_1111_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_args_1091_);
lean_inc(v_fn_1090_);
lean_dec(v_value_1022_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1111_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = 1;
if (v_isShared_1094_ == 0)
{
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fn_1090_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_args_1091_);
v___x_1097_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1004_);
v___x_1099_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1095_, v___x_1097_, v___x_1098_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = 2;
v___x_1101_ = lean_box(v___x_1100_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1101_);
v___x_1103_ = v___x_1088_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
else
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1105_ = 0;
v___x_1106_ = lean_box(v___x_1105_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1106_);
v___x_1108_ = v___x_1088_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1139_; 
v_isSharedCheck_1139_ = !lean_is_exclusive(v_instr_1003_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; 
v_unused_1140_ = lean_ctor_get(v_instr_1003_, 0);
lean_dec(v_unused_1140_);
v___x_1115_ = v_instr_1003_;
v_isShared_1116_ = v_isSharedCheck_1139_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v_instr_1003_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1139_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_fvarId_1117_; lean_object* v_args_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1138_; 
v_fvarId_1117_ = lean_ctor_get(v_value_1022_, 0);
v_args_1118_ = lean_ctor_get(v_value_1022_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_value_1022_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1120_ = v_value_1022_;
v_isShared_1121_ = v_isSharedCheck_1138_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_args_1118_);
lean_inc(v_fvarId_1117_);
lean_dec(v_value_1022_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1138_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = 1;
if (v_isShared_1121_ == 0)
{
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_fvarId_1117_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_args_1118_);
v___x_1124_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1004_);
v___x_1126_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v___x_1122_, v___x_1124_, v___x_1125_);
lean_dec(v___x_1125_);
lean_dec_ref(v___x_1124_);
if (v___x_1126_ == 0)
{
uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = 2;
v___x_1128_ = lean_box(v___x_1127_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1128_);
v___x_1130_ = v___x_1115_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = 0;
v___x_1133_ = lean_box(v___x_1132_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1133_);
v___x_1135_ = v___x_1115_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
default: 
{
lean_dec(v_value_1022_);
goto v___jp_1011_;
}
}
}
else
{
goto v___jp_1011_;
}
v___jp_1011_:
{
uint8_t v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1012_ = 1;
v___x_1013_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_x_1004_);
v___x_1014_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_1012_, v_instr_1003_, v___x_1013_);
lean_dec(v___x_1013_);
lean_dec_ref(v_instr_1003_);
if (v___x_1014_ == 0)
{
uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = 2;
v___x_1016_ = lean_box(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
else
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = 1;
v___x_1019_ = lean_box(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse___boxed(lean_object* v_instr_1141_, lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1141_, v_x_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(lean_object* v_x_1150_, lean_object* v_as_1151_, size_t v_sz_1152_, size_t v_i_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___redArg(v_x_1150_, v_as_1151_, v_sz_1152_, v_i_1153_, v_b_1154_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0___boxed(lean_object* v_x_1162_, lean_object* v_as_1163_, lean_object* v_sz_1164_, lean_object* v_i_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
size_t v_sz_boxed_1173_; size_t v_i_boxed_1174_; lean_object* v_res_1175_; 
v_sz_boxed_1173_ = lean_unbox_usize(v_sz_1164_);
lean_dec(v_sz_1164_);
v_i_boxed_1174_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse_spec__0(v_x_1162_, v_as_1163_, v_sz_boxed_1173_, v_i_boxed_1174_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_as_1163_);
lean_dec(v_x_1162_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(lean_object* v_alt_1176_, lean_object* v_f_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___y_1185_; 
switch(lean_obj_tag(v_alt_1176_))
{
case 0:
{
lean_object* v_code_1204_; 
v_code_1204_ = lean_ctor_get(v_alt_1176_, 2);
lean_inc_ref(v_code_1204_);
v___y_1185_ = v_code_1204_;
goto v___jp_1184_;
}
case 1:
{
lean_object* v_code_1205_; 
v_code_1205_ = lean_ctor_get(v_alt_1176_, 1);
lean_inc_ref(v_code_1205_);
v___y_1185_ = v_code_1205_;
goto v___jp_1184_;
}
default: 
{
lean_object* v_code_1206_; 
v_code_1206_ = lean_ctor_get(v_alt_1176_, 0);
lean_inc_ref(v_code_1206_);
v___y_1185_ = v_code_1206_;
goto v___jp_1184_;
}
}
v___jp_1184_:
{
lean_object* v___x_1186_; 
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
lean_inc_ref(v___y_1178_);
v___x_1186_ = lean_apply_7(v_f_1177_, v___y_1185_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, lean_box(0));
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1195_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_alt_1176_, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_alt_1176_);
v_a_1196_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1186_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1186_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg___boxed(lean_object* v_alt_1207_, lean_object* v_f_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_alt_1207_, v_f_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed(lean_object* v_x_1216_, lean_object* v_info_1217_, lean_object* v_c_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_x_1216_, v_info_1217_, v_c_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec_ref(v_a_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(lean_object* v_x_1226_, lean_object* v_info_1227_, lean_object* v_i_1228_, lean_object* v_as_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_array_get_size(v_as_1229_);
v___x_1237_ = lean_nat_dec_lt(v_i_1228_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec(v_i_1228_);
lean_dec_ref(v_info_1227_);
lean_dec(v_x_1226_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_as_1229_);
return v___x_1238_;
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1239_ = lean_array_fget_borrowed(v_as_1229_, v_i_1228_);
lean_inc_ref(v_info_1227_);
lean_inc(v_x_1226_);
v___x_1240_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D___boxed), 9, 2);
lean_closure_set(v___x_1240_, 0, v_x_1226_);
lean_closure_set(v___x_1240_, 1, v_info_1227_);
lean_inc(v_a_1239_);
v___x_1241_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_a_1239_, v___x_1240_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; size_t v___x_1243_; size_t v___x_1244_; uint8_t v___x_1245_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_ptr_addr(v_a_1239_);
v___x_1244_ = lean_ptr_addr(v_a_1242_);
v___x_1245_ = lean_usize_dec_eq(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_i_1228_, v___x_1246_);
v___x_1248_ = lean_array_fset(v_as_1229_, v_i_1228_, v_a_1242_);
lean_dec(v_i_1228_);
v_i_1228_ = v___x_1247_;
v_as_1229_ = v___x_1248_;
goto _start;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_a_1242_);
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v_i_1228_, v___x_1250_);
lean_dec(v_i_1228_);
v_i_1228_ = v___x_1251_;
goto _start;
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref(v_as_1229_);
lean_dec(v_i_1228_);
lean_dec_ref(v_info_1227_);
lean_dec(v_x_1226_);
v_a_1253_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1241_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1241_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_1263_ = lean_unsigned_to_nat(61u);
v___x_1264_ = lean_unsigned_to_nat(247u);
v___x_1265_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__0));
v___x_1266_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_1267_ = l_mkPanicMessageWithDecl(v___x_1266_, v___x_1265_, v___x_1264_, v___x_1263_, v___x_1262_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(lean_object* v_x_1268_, lean_object* v_info_1269_, lean_object* v_c_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
switch(lean_obj_tag(v_c_1270_))
{
case 0:
{
lean_object* v_decl_1277_; lean_object* v_k_1278_; uint8_t v___x_1279_; lean_object* v_instr_1280_; uint8_t v___x_1281_; uint8_t v___x_1282_; 
v_decl_1277_ = lean_ctor_get(v_c_1270_, 0);
v_k_1278_ = lean_ctor_get(v_c_1270_, 1);
v___x_1279_ = 1;
v_instr_1280_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1279_, v_c_1270_);
lean_inc(v_x_1268_);
v___x_1281_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1280_, v_x_1268_);
v___x_1282_ = 1;
if (v___x_1281_ == 0)
{
lean_object* v___x_1283_; 
lean_inc_ref(v_k_1278_);
lean_inc_ref(v_info_1269_);
lean_inc(v_x_1268_);
v___x_1283_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1268_, v_info_1269_, v_k_1278_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1401_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1401_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1401_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___y_1289_; lean_object* v_snd_1295_; uint8_t v___x_1296_; 
v_snd_1295_ = lean_ctor_get(v_a_1284_, 1);
v___x_1296_ = lean_unbox(v_snd_1295_);
if (v___x_1296_ == 0)
{
lean_object* v_fst_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1386_; 
lean_inc(v_snd_1295_);
lean_del_object(v___x_1286_);
v_fst_1297_ = lean_ctor_get(v_a_1284_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_a_1284_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_a_1284_, 1);
lean_dec(v_unused_1387_);
v___x_1299_ = v_a_1284_;
v_isShared_1300_ = v_isSharedCheck_1386_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_fst_1297_);
lean_dec(v_a_1284_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1386_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; 
lean_inc(v_x_1268_);
v___x_1301_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1280_, v_x_1268_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1377_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1377_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1377_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___y_1307_; lean_object* v___y_1315_; uint8_t v___x_1319_; 
v___x_1319_ = lean_unbox(v_a_1302_);
lean_dec(v_a_1302_);
switch(v___x_1319_)
{
case 0:
{
size_t v___x_1320_; size_t v___x_1321_; uint8_t v___x_1322_; 
lean_del_object(v___x_1304_);
lean_del_object(v___x_1299_);
lean_dec(v_snd_1295_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1320_ = lean_ptr_addr(v_k_1278_);
v___x_1321_ = lean_ptr_addr(v_fst_1297_);
v___x_1322_ = lean_usize_dec_eq(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_inc_ref(v_decl_1277_);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; lean_object* v_unused_1331_; 
v_unused_1330_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1331_);
v___x_1324_ = v_c_1270_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v_c_1270_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_fst_1297_);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_decl_1277_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_fst_1297_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
v___y_1315_ = v___x_1327_;
goto v___jp_1314_;
}
}
}
else
{
lean_dec(v_fst_1297_);
v___y_1315_ = v_c_1270_;
goto v___jp_1314_;
}
}
case 1:
{
lean_object* v___x_1332_; 
lean_del_object(v___x_1304_);
lean_del_object(v___x_1299_);
lean_dec(v_snd_1295_);
v___x_1332_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1268_, v_info_1269_, v_fst_1297_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec_ref(v_info_1269_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1356_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1356_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1356_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___y_1338_; size_t v___x_1344_; size_t v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_ptr_addr(v_k_1278_);
v___x_1345_ = lean_ptr_addr(v_a_1333_);
v___x_1346_ = lean_usize_dec_eq(v___x_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_inc_ref(v_decl_1277_);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1354_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1355_);
v___x_1348_ = v_c_1270_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v_c_1270_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v_a_1333_);
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_decl_1277_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_a_1333_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v___y_1338_ = v___x_1351_;
goto v___jp_1337_;
}
}
}
else
{
lean_dec(v_a_1333_);
v___y_1338_ = v_c_1270_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_box(v___x_1282_);
v___x_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___y_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1340_);
v___x_1342_ = v___x_1335_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref_known(v_c_1270_, 2);
v_a_1357_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1332_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1332_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
default: 
{
size_t v___x_1365_; size_t v___x_1366_; uint8_t v___x_1367_; 
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1365_ = lean_ptr_addr(v_k_1278_);
v___x_1366_ = lean_ptr_addr(v_fst_1297_);
v___x_1367_ = lean_usize_dec_eq(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_inc_ref(v_decl_1277_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1376_);
v___x_1369_ = v_c_1270_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v_c_1270_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_fst_1297_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_decl_1277_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_fst_1297_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v___y_1307_ = v___x_1372_;
goto v___jp_1306_;
}
}
}
else
{
lean_dec(v_fst_1297_);
v___y_1307_ = v_c_1270_;
goto v___jp_1306_;
}
}
}
v___jp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___y_1307_);
v___x_1309_ = v___x_1299_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___y_1307_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_snd_1295_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1309_);
v___x_1311_ = v___x_1304_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
v___jp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_box(v___x_1282_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___y_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_del_object(v___x_1299_);
lean_dec(v_fst_1297_);
lean_dec(v_snd_1295_);
lean_dec_ref_known(v_c_1270_, 2);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v_a_1378_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1301_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1301_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
else
{
lean_object* v_fst_1388_; size_t v___x_1389_; size_t v___x_1390_; uint8_t v___x_1391_; 
lean_dec_ref(v_instr_1280_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v_fst_1388_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_fst_1388_);
lean_dec(v_a_1284_);
v___x_1389_ = lean_ptr_addr(v_k_1278_);
v___x_1390_ = lean_ptr_addr(v_fst_1388_);
v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_inc_ref(v_decl_1277_);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1400_);
v___x_1393_ = v_c_1270_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_c_1270_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v_fst_1388_);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_decl_1277_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_fst_1388_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v___y_1289_ = v___x_1396_;
goto v___jp_1288_;
}
}
}
else
{
lean_dec(v_fst_1388_);
v___y_1289_ = v_c_1270_;
goto v___jp_1288_;
}
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_box(v___x_1282_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___y_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1291_);
v___x_1293_ = v___x_1286_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_dec_ref(v_instr_1280_);
lean_dec_ref_known(v_c_1270_, 2);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
return v___x_1283_;
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v_instr_1280_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1402_ = lean_box(v___x_1282_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_c_1270_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
case 2:
{
lean_object* v_decl_1405_; lean_object* v_k_1406_; lean_object* v___x_1407_; 
v_decl_1405_ = lean_ctor_get(v_c_1270_, 0);
v_k_1406_ = lean_ctor_get(v_c_1270_, 1);
lean_inc_ref(v_k_1406_);
lean_inc_ref(v_info_1269_);
lean_inc(v_x_1268_);
v___x_1407_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1268_, v_info_1269_, v_k_1406_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v_params_1411_; lean_object* v_type_1412_; lean_object* v_value_1413_; lean_object* v___x_1414_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v_fst_1409_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_fst_1409_);
v_snd_1410_ = lean_ctor_get(v_a_1408_, 1);
lean_inc(v_snd_1410_);
lean_dec(v_a_1408_);
v_params_1411_ = lean_ctor_get(v_decl_1405_, 2);
v_type_1412_ = lean_ctor_get(v_decl_1405_, 3);
v_value_1413_ = lean_ctor_get(v_decl_1405_, 4);
lean_inc_ref(v_value_1413_);
v___x_1414_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1268_, v_info_1269_, v_value_1413_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v_fst_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1460_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v_fst_1416_ = lean_ctor_get(v_a_1415_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1415_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_a_1415_, 1);
lean_dec(v_unused_1461_);
v___x_1418_ = v_a_1415_;
v_isShared_1419_ = v_isSharedCheck_1460_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_fst_1416_);
lean_dec(v_a_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1460_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = 1;
lean_inc_ref(v_params_1411_);
lean_inc_ref(v_type_1412_);
lean_inc_ref(v_decl_1405_);
v___x_1421_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1420_, v_decl_1405_, v_type_1412_, v_params_1411_, v_fst_1416_, v_a_1273_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1451_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1451_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1451_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___y_1427_; uint8_t v___y_1435_; size_t v___x_1445_; size_t v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = lean_ptr_addr(v_k_1406_);
v___x_1446_ = lean_ptr_addr(v_fst_1409_);
v___x_1447_ = lean_usize_dec_eq(v___x_1445_, v___x_1446_);
if (v___x_1447_ == 0)
{
v___y_1435_ = v___x_1447_;
goto v___jp_1434_;
}
else
{
size_t v___x_1448_; size_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = lean_ptr_addr(v_decl_1405_);
v___x_1449_ = lean_ptr_addr(v_a_1422_);
v___x_1450_ = lean_usize_dec_eq(v___x_1448_, v___x_1449_);
v___y_1435_ = v___x_1450_;
goto v___jp_1434_;
}
v___jp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_snd_1410_);
lean_ctor_set(v___x_1418_, 0, v___y_1427_);
v___x_1429_ = v___x_1418_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___y_1427_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_snd_1410_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1429_);
v___x_1431_ = v___x_1424_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
v___jp_1434_:
{
if (v___y_1435_ == 0)
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_isSharedCheck_1442_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; lean_object* v_unused_1444_; 
v_unused_1443_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1444_);
v___x_1437_ = v_c_1270_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_c_1270_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_fst_1409_);
lean_ctor_set(v___x_1437_, 0, v_a_1422_);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1422_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_fst_1409_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v___y_1427_ = v___x_1440_;
goto v___jp_1426_;
}
}
}
else
{
lean_dec(v_a_1422_);
lean_dec(v_fst_1409_);
v___y_1427_ = v_c_1270_;
goto v___jp_1426_;
}
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_del_object(v___x_1418_);
lean_dec(v_snd_1410_);
lean_dec(v_fst_1409_);
lean_dec_ref_known(v_c_1270_, 2);
v_a_1452_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1421_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1421_);
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
lean_dec(v_snd_1410_);
lean_dec(v_fst_1409_);
lean_dec_ref_known(v_c_1270_, 2);
return v___x_1414_;
}
}
else
{
lean_dec_ref_known(v_c_1270_, 2);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
return v___x_1407_;
}
}
case 3:
{
lean_object* v___x_1462_; 
lean_dec_ref(v_info_1269_);
lean_inc_ref(v_c_1270_);
v___x_1462_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1270_, v_x_1268_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_ctor_set(v___x_1467_, 0, v_c_1270_);
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
lean_dec_ref_known(v_c_1270_, 2);
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
v_cases_1480_ = lean_ctor_get(v_c_1270_, 0);
lean_inc_ref(v_cases_1480_);
lean_inc(v_x_1268_);
lean_inc_ref(v_c_1270_);
v___x_1481_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1270_, v_x_1268_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_c_1270_);
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
v___x_1499_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__1(v_x_1268_, v_info_1269_, v___x_1498_, v_alts_1494_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
v_isSharedCheck_1522_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1523_);
v___x_1514_ = v_c_1270_;
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1505_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 1);
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
lean_dec_ref_known(v_c_1270_, 1);
lean_dec_ref(v_cases_1480_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
lean_dec_ref(v_info_1269_);
lean_inc_ref(v_c_1270_);
v___x_1543_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1270_, v_x_1268_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_ctor_set(v___x_1548_, 0, v_c_1270_);
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
lean_dec_ref_known(v_c_1270_, 1);
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
lean_dec_ref(v_info_1269_);
lean_inc_ref(v_c_1270_);
v___x_1561_ = l_Lean_Compiler_LCNF_Code_isFVarLiveIn(v_c_1270_, v_x_1268_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_ctor_set(v___x_1566_, 0, v_c_1270_);
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
lean_dec_ref_known(v_c_1270_, 1);
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
v_fvarId_1579_ = lean_ctor_get(v_c_1270_, 0);
v_i_1580_ = lean_ctor_get(v_c_1270_, 1);
v_y_1581_ = lean_ctor_get(v_c_1270_, 2);
v_k_1582_ = lean_ctor_get(v_c_1270_, 3);
v___x_1583_ = 1;
v_instr_1584_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1583_, v_c_1270_);
lean_inc(v_x_1268_);
v___x_1585_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1584_, v_x_1268_);
v___x_1586_ = 1;
if (v___x_1585_ == 0)
{
lean_object* v___x_1587_; 
lean_inc_ref(v_k_1582_);
lean_inc_ref(v_info_1269_);
lean_inc(v_x_1268_);
v___x_1587_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1268_, v_info_1269_, v_k_1582_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_inc(v_x_1268_);
v___x_1605_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1584_, v_x_1268_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1624_ = lean_ptr_addr(v_k_1582_);
v___x_1625_ = lean_ptr_addr(v_fst_1601_);
v___x_1626_ = lean_usize_dec_eq(v___x_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_inc(v_y_1581_);
lean_inc(v_i_1580_);
lean_inc(v_fvarId_1579_);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; lean_object* v_unused_1636_; lean_object* v_unused_1637_; 
v_unused_1634_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1637_);
v___x_1628_ = v_c_1270_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1619_ = v_c_1270_;
goto v___jp_1618_;
}
}
case 1:
{
lean_object* v___x_1638_; 
lean_del_object(v___x_1608_);
lean_del_object(v___x_1603_);
lean_dec(v_snd_1599_);
v___x_1638_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1268_, v_info_1269_, v_fst_1601_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec_ref(v_info_1269_);
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
v_isSharedCheck_1659_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1660_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1663_);
v___x_1654_ = v_c_1270_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1644_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 4);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1673_ = lean_ptr_addr(v_k_1582_);
v___x_1674_ = lean_ptr_addr(v_fst_1601_);
v___x_1675_ = lean_usize_dec_eq(v___x_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_inc(v_y_1581_);
lean_inc(v_i_1580_);
lean_inc(v_fvarId_1579_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1683_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1686_);
v___x_1677_ = v_c_1270_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1611_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 4);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
v_isSharedCheck_1708_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; 
v_unused_1709_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1712_);
v___x_1703_ = v_c_1270_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1593_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 4);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
return v___x_1587_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref(v_instr_1584_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1714_ = lean_box(v___x_1586_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_c_1270_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
case 9:
{
lean_object* v_fvarId_1717_; lean_object* v_i_1718_; lean_object* v_offset_1719_; lean_object* v_y_1720_; lean_object* v_ty_1721_; lean_object* v_k_1722_; uint8_t v___x_1723_; lean_object* v_instr_1724_; uint8_t v___x_1725_; uint8_t v___x_1726_; 
v_fvarId_1717_ = lean_ctor_get(v_c_1270_, 0);
v_i_1718_ = lean_ctor_get(v_c_1270_, 1);
v_offset_1719_ = lean_ctor_get(v_c_1270_, 2);
v_y_1720_ = lean_ctor_get(v_c_1270_, 3);
v_ty_1721_ = lean_ctor_get(v_c_1270_, 4);
v_k_1722_ = lean_ctor_get(v_c_1270_, 5);
v___x_1723_ = 1;
v_instr_1724_ = l_Lean_Compiler_LCNF_Code_toCodeDecl_x21(v___x_1723_, v_c_1270_);
lean_inc(v_x_1268_);
v___x_1725_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_isCtorUsing(v_instr_1724_, v_x_1268_);
v___x_1726_ = 1;
if (v___x_1725_ == 0)
{
lean_object* v___x_1727_; 
lean_inc_ref(v_k_1722_);
lean_inc_ref(v_info_1269_);
lean_inc(v_x_1268_);
v___x_1727_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go(v_x_1268_, v_info_1269_, v_k_1722_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_inc(v_x_1268_);
v___x_1745_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_classifyUse(v_instr_1724_, v_x_1268_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
v_isSharedCheck_1773_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; 
v_unused_1774_ = lean_ctor_get(v_c_1270_, 5);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_c_1270_, 4);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1779_);
v___x_1768_ = v_c_1270_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1759_ = v_c_1270_;
goto v___jp_1758_;
}
}
case 1:
{
lean_object* v___x_1780_; 
lean_del_object(v___x_1748_);
lean_del_object(v___x_1743_);
lean_dec(v_snd_1739_);
v___x_1780_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S(v_x_1268_, v_info_1269_, v_fst_1741_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec_ref(v_info_1269_);
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
v_isSharedCheck_1801_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; lean_object* v_unused_1806_; lean_object* v_unused_1807_; 
v_unused_1802_ = lean_ctor_get(v_c_1270_, 5);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_c_1270_, 4);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1805_);
v_unused_1806_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1807_);
v___x_1796_ = v_c_1270_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1786_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 6);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
v_isSharedCheck_1826_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; 
v_unused_1827_ = lean_ctor_get(v_c_1270_, 5);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_c_1270_, 4);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1829_);
v_unused_1830_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1832_);
v___x_1821_ = v_c_1270_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1751_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 6);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
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
v_isSharedCheck_1854_ = !lean_is_exclusive(v_c_1270_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1855_ = lean_ctor_get(v_c_1270_, 5);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_c_1270_, 4);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_c_1270_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_c_1270_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_c_1270_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_c_1270_, 0);
lean_dec(v_unused_1860_);
v___x_1849_ = v_c_1270_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v_c_1270_);
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
v___y_1733_ = v_c_1270_;
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
lean_dec_ref_known(v_c_1270_, 6);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
return v___x_1727_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_instr_1724_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1862_ = lean_box(v___x_1726_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_c_1270_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
default: 
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec_ref(v_c_1270_);
lean_dec_ref(v_info_1269_);
lean_dec(v_x_1268_);
v___x_1865_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go___closed__1);
v___x_1866_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3(v___x_1865_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
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
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_5620__overap_1977_; lean_object* v___x_1978_; 
v___x_1972_ = l_StateRefT_x27_instMonad___redArg(v___x_1971_);
v___x_1973_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__0___closed__0);
v___x_1974_ = l_instInhabitedOfMonad___redArg(v___x_1972_, v___x_1973_);
v___f_1975_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1975_, 0, v___x_1974_);
v___f_1976_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1976_, 0, v___f_1975_);
v___x_5620__overap_1977_ = lean_panic_fn_borrowed(v___f_1976_, v_msg_1940_);
lean_dec_ref(v___f_1976_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1944_);
lean_inc(v___y_1943_);
lean_inc_ref(v___y_1942_);
lean_inc_ref(v___y_1941_);
v___x_1978_ = lean_apply_6(v___x_5620__overap_1977_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, lean_box(0));
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
v___x_2063_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_2115_; lean_object* v_vs_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2136_; 
v_ks_2115_ = lean_ctor_get(v_x_2064_, 0);
v_vs_2116_ = lean_ctor_get(v_x_2064_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2118_ = v_x_2064_;
v_isShared_2119_ = v_isSharedCheck_2136_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_vs_2116_);
lean_inc(v_ks_2115_);
lean_dec(v_x_2064_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2136_;
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
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_ks_2115_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_vs_2116_);
v___x_2121_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v_newNode_2122_; uint8_t v___y_2124_; size_t v___x_2130_; uint8_t v___x_2131_; 
v_newNode_2122_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_2121_, v_x_2067_, v_x_2068_);
v___x_2130_ = ((size_t)7ULL);
v___x_2131_ = lean_usize_dec_le(v___x_2130_, v_x_2066_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2122_);
v___x_2133_ = lean_unsigned_to_nat(4u);
v___x_2134_ = lean_nat_dec_lt(v___x_2132_, v___x_2133_);
lean_dec(v___x_2132_);
v___y_2124_ = v___x_2134_;
goto v___jp_2123_;
}
else
{
v___y_2124_ = v___x_2131_;
goto v___jp_2123_;
}
v___jp_2123_:
{
if (v___y_2124_ == 0)
{
lean_object* v_ks_2125_; lean_object* v_vs_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_ks_2125_ = lean_ctor_get(v_newNode_2122_, 0);
lean_inc_ref(v_ks_2125_);
v_vs_2126_ = lean_ctor_get(v_newNode_2122_, 1);
lean_inc_ref(v_vs_2126_);
lean_dec_ref(v_newNode_2122_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2129_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_2066_, v_ks_2125_, v_vs_2126_, v___x_2127_, v___x_2128_);
lean_dec_ref(v_vs_2126_);
lean_dec_ref(v_ks_2125_);
return v___x_2129_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t v_depth_2137_, lean_object* v_keys_2138_, lean_object* v_vals_2139_, lean_object* v_i_2140_, lean_object* v_entries_2141_){
_start:
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = lean_array_get_size(v_keys_2138_);
v___x_2143_ = lean_nat_dec_lt(v_i_2140_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_dec(v_i_2140_);
return v_entries_2141_;
}
else
{
lean_object* v_k_2144_; lean_object* v_v_2145_; uint64_t v___x_2146_; size_t v_h_2147_; size_t v___x_2148_; lean_object* v___x_2149_; size_t v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; size_t v_h_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_k_2144_ = lean_array_fget_borrowed(v_keys_2138_, v_i_2140_);
v_v_2145_ = lean_array_fget_borrowed(v_vals_2139_, v_i_2140_);
v___x_2146_ = l_Lean_instHashableFVarId_hash(v_k_2144_);
v_h_2147_ = lean_uint64_to_usize(v___x_2146_);
v___x_2148_ = ((size_t)5ULL);
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = ((size_t)1ULL);
v___x_2151_ = lean_usize_sub(v_depth_2137_, v___x_2150_);
v___x_2152_ = lean_usize_mul(v___x_2148_, v___x_2151_);
v_h_2153_ = lean_usize_shift_right(v_h_2147_, v___x_2152_);
v___x_2154_ = lean_nat_add(v_i_2140_, v___x_2149_);
lean_dec(v_i_2140_);
lean_inc(v_v_2145_);
lean_inc(v_k_2144_);
v___x_2155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2141_, v_h_2153_, v_depth_2137_, v_k_2144_, v_v_2145_);
v_i_2140_ = v___x_2154_;
v_entries_2141_ = v___x_2155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_2157_, lean_object* v_keys_2158_, lean_object* v_vals_2159_, lean_object* v_i_2160_, lean_object* v_entries_2161_){
_start:
{
size_t v_depth_boxed_2162_; lean_object* v_res_2163_; 
v_depth_boxed_2162_ = lean_unbox_usize(v_depth_2157_);
lean_dec(v_depth_2157_);
v_res_2163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2162_, v_keys_2158_, v_vals_2159_, v_i_2160_, v_entries_2161_);
lean_dec_ref(v_vals_2159_);
lean_dec_ref(v_keys_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
size_t v_x_6230__boxed_2169_; size_t v_x_6231__boxed_2170_; lean_object* v_res_2171_; 
v_x_6230__boxed_2169_ = lean_unbox_usize(v_x_2165_);
lean_dec(v_x_2165_);
v_x_6231__boxed_2170_ = lean_unbox_usize(v_x_2166_);
lean_dec(v_x_2166_);
v_res_2171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2164_, v_x_6230__boxed_2169_, v_x_6231__boxed_2170_, v_x_2167_, v_x_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
uint64_t v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = l_Lean_instHashableFVarId_hash(v_x_2173_);
v___x_2176_ = lean_uint64_to_usize(v___x_2175_);
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2172_, v___x_2176_, v___x_2177_, v_x_2173_, v_x_2174_);
return v___x_2178_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2179_, lean_object* v_i_2180_, lean_object* v_k_2181_){
_start:
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_array_get_size(v_keys_2179_);
v___x_2183_ = lean_nat_dec_lt(v_i_2180_, v___x_2182_);
if (v___x_2183_ == 0)
{
lean_dec(v_i_2180_);
return v___x_2183_;
}
else
{
lean_object* v_k_x27_2184_; uint8_t v___x_2185_; 
v_k_x27_2184_ = lean_array_fget_borrowed(v_keys_2179_, v_i_2180_);
v___x_2185_ = l_Lean_instBEqFVarId_beq(v_k_2181_, v_k_x27_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_add(v_i_2180_, v___x_2186_);
lean_dec(v_i_2180_);
v_i_2180_ = v___x_2187_;
goto _start;
}
else
{
lean_dec(v_i_2180_);
return v___x_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2189_, lean_object* v_i_2190_, lean_object* v_k_2191_){
_start:
{
uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_res_2192_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2189_, v_i_2190_, v_k_2191_);
lean_dec(v_k_2191_);
lean_dec_ref(v_keys_2189_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2194_, size_t v_x_2195_, lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v_es_2197_; lean_object* v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; lean_object* v_j_2201_; lean_object* v___x_2202_; 
v_es_2197_ = lean_ctor_get(v_x_2194_, 0);
v___x_2198_ = lean_box(2);
v___x_2199_ = ((size_t)31ULL);
v___x_2200_ = lean_usize_land(v_x_2195_, v___x_2199_);
v_j_2201_ = lean_usize_to_nat(v___x_2200_);
v___x_2202_ = lean_array_get_borrowed(v___x_2198_, v_es_2197_, v_j_2201_);
lean_dec(v_j_2201_);
switch(lean_obj_tag(v___x_2202_))
{
case 0:
{
lean_object* v_key_2203_; uint8_t v___x_2204_; 
v_key_2203_ = lean_ctor_get(v___x_2202_, 0);
v___x_2204_ = l_Lean_instBEqFVarId_beq(v_x_2196_, v_key_2203_);
return v___x_2204_;
}
case 1:
{
lean_object* v_node_2205_; size_t v___x_2206_; size_t v___x_2207_; 
v_node_2205_ = lean_ctor_get(v___x_2202_, 0);
v___x_2206_ = ((size_t)5ULL);
v___x_2207_ = lean_usize_shift_right(v_x_2195_, v___x_2206_);
v_x_2194_ = v_node_2205_;
v_x_2195_ = v___x_2207_;
goto _start;
}
default: 
{
uint8_t v___x_2209_; 
v___x_2209_ = 0;
return v___x_2209_;
}
}
}
else
{
lean_object* v_ks_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_ks_2210_ = lean_ctor_get(v_x_2194_, 0);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2210_, v___x_2211_, v_x_2196_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
size_t v_x_6412__boxed_2216_; uint8_t v_res_2217_; lean_object* v_r_2218_; 
v_x_6412__boxed_2216_ = lean_unbox_usize(v_x_2214_);
lean_dec(v_x_2214_);
v_res_2217_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2213_, v_x_6412__boxed_2216_, v_x_2215_);
lean_dec(v_x_2215_);
lean_dec_ref(v_x_2213_);
v_r_2218_ = lean_box(v_res_2217_);
return v_r_2218_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2219_, lean_object* v_x_2220_){
_start:
{
uint64_t v___x_2221_; size_t v___x_2222_; uint8_t v___x_2223_; 
v___x_2221_ = l_Lean_instHashableFVarId_hash(v_x_2220_);
v___x_2222_ = lean_uint64_to_usize(v___x_2221_);
v___x_2223_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2219_, v___x_2222_, v_x_2220_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
uint8_t v_res_2226_; lean_object* v_r_2227_; 
v_res_2226_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2224_, v_x_2225_);
lean_dec(v_x_2225_);
lean_dec_ref(v_x_2224_);
v_r_2227_ = lean_box(v_res_2226_);
return v_r_2227_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2230_ = lean_unsigned_to_nat(59u);
v___x_2231_ = lean_unsigned_to_nat(281u);
v___x_2232_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2233_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2234_ = l_mkPanicMessageWithDecl(v___x_2233_, v___x_2232_, v___x_2231_, v___x_2230_, v___x_2229_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
switch(lean_obj_tag(v_c_2235_))
{
case 0:
{
lean_object* v_decl_2242_; lean_object* v_k_2243_; lean_object* v___x_2244_; 
v_decl_2242_ = lean_ctor_get(v_c_2235_, 0);
v_k_2243_ = lean_ctor_get(v_c_2235_, 1);
lean_inc_ref(v_k_2243_);
v___x_2244_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2243_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2267_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2267_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2267_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
size_t v___x_2249_; size_t v___x_2250_; uint8_t v___x_2251_; 
v___x_2249_ = lean_ptr_addr(v_k_2243_);
v___x_2250_ = lean_ptr_addr(v_a_2245_);
v___x_2251_ = lean_usize_dec_eq(v___x_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2261_; 
lean_inc_ref(v_decl_2242_);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_c_2235_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2262_ = lean_ctor_get(v_c_2235_, 1);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_c_2235_, 0);
lean_dec(v_unused_2263_);
v___x_2253_ = v_c_2235_;
v_isShared_2254_ = v_isSharedCheck_2261_;
goto v_resetjp_2252_;
}
else
{
lean_dec(v_c_2235_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2261_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v_a_2245_);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_decl_2242_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_a_2245_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2258_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2256_);
v___x_2258_ = v___x_2247_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v___x_2265_; 
lean_dec(v_a_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_c_2235_);
v___x_2265_ = v___x_2247_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_c_2235_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2235_, 2);
return v___x_2244_;
}
}
case 2:
{
lean_object* v_decl_2268_; lean_object* v_k_2269_; lean_object* v_params_2270_; lean_object* v_type_2271_; lean_object* v_value_2272_; lean_object* v___x_2273_; 
v_decl_2268_ = lean_ctor_get(v_c_2235_, 0);
v_k_2269_ = lean_ctor_get(v_c_2235_, 1);
v_params_2270_ = lean_ctor_get(v_decl_2268_, 2);
v_type_2271_ = lean_ctor_get(v_decl_2268_, 3);
v_value_2272_ = lean_ctor_get(v_decl_2268_, 4);
lean_inc_ref(v_value_2272_);
v___x_2273_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2272_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2275_ = 1;
lean_inc_ref(v_params_2270_);
lean_inc_ref(v_type_2271_);
lean_inc_ref(v_decl_2268_);
v___x_2276_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2275_, v_decl_2268_, v_type_2271_, v_params_2270_, v_a_2274_, v_a_2238_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
lean_inc_ref(v_k_2269_);
v___x_2278_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2269_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2306_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2306_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2306_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
uint8_t v___y_2284_; size_t v___x_2300_; size_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = lean_ptr_addr(v_k_2269_);
v___x_2301_ = lean_ptr_addr(v_a_2279_);
v___x_2302_ = lean_usize_dec_eq(v___x_2300_, v___x_2301_);
if (v___x_2302_ == 0)
{
v___y_2284_ = v___x_2302_;
goto v___jp_2283_;
}
else
{
size_t v___x_2303_; size_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2303_ = lean_ptr_addr(v_decl_2268_);
v___x_2304_ = lean_ptr_addr(v_a_2277_);
v___x_2305_ = lean_usize_dec_eq(v___x_2303_, v___x_2304_);
v___y_2284_ = v___x_2305_;
goto v___jp_2283_;
}
v___jp_2283_:
{
if (v___y_2284_ == 0)
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2294_; 
v_isSharedCheck_2294_ = !lean_is_exclusive(v_c_2235_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2295_ = lean_ctor_get(v_c_2235_, 1);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_c_2235_, 0);
lean_dec(v_unused_2296_);
v___x_2286_ = v_c_2235_;
v_isShared_2287_ = v_isSharedCheck_2294_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v_c_2235_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2294_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 1, v_a_2279_);
lean_ctor_set(v___x_2286_, 0, v_a_2277_);
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2277_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_a_2279_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2289_);
v___x_2291_ = v___x_2281_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v___x_2298_; 
lean_dec(v_a_2279_);
lean_dec(v_a_2277_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_c_2235_);
v___x_2298_ = v___x_2281_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_c_2235_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
else
{
lean_dec(v_a_2277_);
lean_dec_ref_known(v_c_2235_, 2);
return v___x_2278_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref_known(v_c_2235_, 2);
v_a_2307_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2276_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2276_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
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
else
{
lean_dec_ref_known(v_c_2235_, 2);
return v___x_2273_;
}
}
case 3:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v_c_2235_);
return v___x_2315_;
}
case 4:
{
lean_object* v_cases_2316_; lean_object* v_typeName_2317_; lean_object* v_resultType_2318_; lean_object* v_discr_2319_; lean_object* v_alts_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2373_; 
v_cases_2316_ = lean_ctor_get(v_c_2235_, 0);
lean_inc_ref(v_cases_2316_);
v_typeName_2317_ = lean_ctor_get(v_cases_2316_, 0);
v_resultType_2318_ = lean_ctor_get(v_cases_2316_, 1);
v_discr_2319_ = lean_ctor_get(v_cases_2316_, 2);
v_alts_2320_ = lean_ctor_get(v_cases_2316_, 3);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_cases_2316_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2322_ = v_cases_2316_;
v_isShared_2323_ = v_isSharedCheck_2373_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_alts_2320_);
lean_inc(v_discr_2319_);
lean_inc(v_resultType_2318_);
lean_inc(v_typeName_2317_);
lean_dec(v_cases_2316_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2373_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_alreadyFound_2324_; uint8_t v_relaxedReuse_2325_; lean_object* v_ownedness_2326_; uint8_t v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; size_t v_sz_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
v_alreadyFound_2324_ = lean_ctor_get(v_a_2236_, 0);
v_relaxedReuse_2325_ = lean_ctor_get_uint8(v_a_2236_, sizeof(void*)*2);
v_ownedness_2326_ = lean_ctor_get(v_a_2236_, 1);
v___x_2327_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2324_, v_discr_2319_);
v___x_2328_ = 0;
v___x_2329_ = lean_box(v___x_2328_);
v___x_2330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2326_, v_discr_2319_, v___x_2329_);
lean_dec(v___x_2329_);
v___x_2331_ = 1;
v___x_2332_ = lean_unbox(v___x_2330_);
lean_dec(v___x_2330_);
v___x_2333_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2332_, v___x_2331_);
v___x_2334_ = lean_box(0);
lean_inc_n(v_discr_2319_, 2);
lean_inc_ref(v_alreadyFound_2324_);
v___x_2335_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2324_, v_discr_2319_, v___x_2334_);
lean_inc_ref(v_ownedness_2326_);
v___x_2336_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v_ownedness_2326_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*2, v_relaxedReuse_2325_);
v_sz_2337_ = lean_array_size(v_alts_2320_);
v___x_2338_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2320_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2333_, v_discr_2319_, v___x_2327_, v_sz_2337_, v___x_2338_, v_alts_2320_, v___x_2336_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec_ref_known(v___x_2336_, 2);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2364_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2364_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2364_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
size_t v___x_2344_; size_t v___x_2345_; uint8_t v___x_2346_; 
v___x_2344_ = lean_ptr_addr(v_alts_2320_);
lean_dec_ref(v_alts_2320_);
v___x_2345_ = lean_ptr_addr(v_a_2340_);
v___x_2346_ = lean_usize_dec_eq(v___x_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2359_; 
v_isSharedCheck_2359_ = !lean_is_exclusive(v_c_2235_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v_c_2235_, 0);
lean_dec(v_unused_2360_);
v___x_2348_ = v_c_2235_;
v_isShared_2349_ = v_isSharedCheck_2359_;
goto v_resetjp_2347_;
}
else
{
lean_dec(v_c_2235_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2359_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 3, v_a_2340_);
v___x_2351_ = v___x_2322_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_typeName_2317_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_resultType_2318_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_discr_2319_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_a_2340_);
v___x_2351_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2351_);
v___x_2353_ = v___x_2348_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2353_);
v___x_2355_ = v___x_2342_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v___x_2362_; 
lean_dec(v_a_2340_);
lean_del_object(v___x_2322_);
lean_dec(v_discr_2319_);
lean_dec_ref(v_resultType_2318_);
lean_dec(v_typeName_2317_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v_c_2235_);
v___x_2362_ = v___x_2342_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_c_2235_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2322_);
lean_dec_ref(v_alts_2320_);
lean_dec(v_discr_2319_);
lean_dec_ref(v_resultType_2318_);
lean_dec(v_typeName_2317_);
lean_dec_ref_known(v_c_2235_, 1);
v_a_2365_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2339_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2339_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
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
}
case 5:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_c_2235_);
return v___x_2374_;
}
case 6:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_c_2235_);
return v___x_2375_;
}
case 8:
{
lean_object* v_fvarId_2376_; lean_object* v_i_2377_; lean_object* v_y_2378_; lean_object* v_k_2379_; lean_object* v___x_2380_; 
v_fvarId_2376_ = lean_ctor_get(v_c_2235_, 0);
v_i_2377_ = lean_ctor_get(v_c_2235_, 1);
v_y_2378_ = lean_ctor_get(v_c_2235_, 2);
v_k_2379_ = lean_ctor_get(v_c_2235_, 3);
lean_inc_ref(v_k_2379_);
v___x_2380_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2379_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2405_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2405_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2405_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
size_t v___x_2385_; size_t v___x_2386_; uint8_t v___x_2387_; 
v___x_2385_ = lean_ptr_addr(v_k_2379_);
v___x_2386_ = lean_ptr_addr(v_a_2381_);
v___x_2387_ = lean_usize_dec_eq(v___x_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2397_; 
lean_inc(v_y_2378_);
lean_inc(v_i_2377_);
lean_inc(v_fvarId_2376_);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_c_2235_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2398_ = lean_ctor_get(v_c_2235_, 3);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_c_2235_, 2);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_c_2235_, 1);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_c_2235_, 0);
lean_dec(v_unused_2401_);
v___x_2389_ = v_c_2235_;
v_isShared_2390_ = v_isSharedCheck_2397_;
goto v_resetjp_2388_;
}
else
{
lean_dec(v_c_2235_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2397_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 3, v_a_2381_);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_fvarId_2376_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_i_2377_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_y_2378_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_a_2381_);
v___x_2392_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2394_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2392_);
v___x_2394_ = v___x_2383_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v___x_2403_; 
lean_dec(v_a_2381_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v_c_2235_);
v___x_2403_ = v___x_2383_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_c_2235_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2235_, 4);
return v___x_2380_;
}
}
case 9:
{
lean_object* v_fvarId_2406_; lean_object* v_i_2407_; lean_object* v_offset_2408_; lean_object* v_y_2409_; lean_object* v_ty_2410_; lean_object* v_k_2411_; lean_object* v___x_2412_; 
v_fvarId_2406_ = lean_ctor_get(v_c_2235_, 0);
v_i_2407_ = lean_ctor_get(v_c_2235_, 1);
v_offset_2408_ = lean_ctor_get(v_c_2235_, 2);
v_y_2409_ = lean_ctor_get(v_c_2235_, 3);
v_ty_2410_ = lean_ctor_get(v_c_2235_, 4);
v_k_2411_ = lean_ctor_get(v_c_2235_, 5);
lean_inc_ref(v_k_2411_);
v___x_2412_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2411_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2439_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2439_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2439_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
size_t v___x_2417_; size_t v___x_2418_; uint8_t v___x_2419_; 
v___x_2417_ = lean_ptr_addr(v_k_2411_);
v___x_2418_ = lean_ptr_addr(v_a_2413_);
v___x_2419_ = lean_usize_dec_eq(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2429_; 
lean_inc_ref(v_ty_2410_);
lean_inc(v_y_2409_);
lean_inc(v_offset_2408_);
lean_inc(v_i_2407_);
lean_inc(v_fvarId_2406_);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_c_2235_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; lean_object* v_unused_2434_; lean_object* v_unused_2435_; 
v_unused_2430_ = lean_ctor_get(v_c_2235_, 5);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_c_2235_, 4);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_c_2235_, 3);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_c_2235_, 2);
lean_dec(v_unused_2433_);
v_unused_2434_ = lean_ctor_get(v_c_2235_, 1);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_c_2235_, 0);
lean_dec(v_unused_2435_);
v___x_2421_ = v_c_2235_;
v_isShared_2422_ = v_isSharedCheck_2429_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v_c_2235_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2429_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 5, v_a_2413_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_fvarId_2406_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_i_2407_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_offset_2408_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_y_2409_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_ty_2410_);
lean_ctor_set(v_reuseFailAlloc_2428_, 5, v_a_2413_);
v___x_2424_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2424_);
v___x_2426_ = v___x_2415_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v___x_2437_; 
lean_dec(v_a_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v_c_2235_);
v___x_2437_ = v___x_2415_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_c_2235_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2235_, 6);
return v___x_2412_;
}
}
default: 
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec_ref(v_c_2235_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2441_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2440_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_a_2443_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2450_, lean_object* v_discr_2451_, uint8_t v___x_2452_, size_t v_sz_2453_, size_t v_i_2454_, lean_object* v_bs_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_lt(v_i_2454_, v_sz_2453_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
lean_dec(v_discr_2451_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_bs_2455_);
return v___x_2463_;
}
else
{
lean_object* v___f_2464_; lean_object* v_v_2465_; lean_object* v___x_2466_; lean_object* v_bs_x27_2467_; lean_object* v_a_2469_; lean_object* v___y_2475_; lean_object* v___x_2485_; 
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2465_ = lean_array_uget(v_bs_2455_, v_i_2454_);
v___x_2466_ = lean_unsigned_to_nat(0u);
v_bs_x27_2467_ = lean_array_uset(v_bs_2455_, v_i_2454_, v___x_2466_);
v___x_2485_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2465_, v___f_2464_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
if (lean_obj_tag(v_a_2486_) == 1)
{
lean_object* v_info_2487_; lean_object* v_code_2488_; uint8_t v___y_2490_; uint8_t v___x_2502_; 
v_info_2487_ = lean_ctor_get(v_a_2486_, 0);
v_code_2488_ = lean_ctor_get(v_a_2486_, 1);
v___x_2502_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2487_);
if (v___x_2502_ == 0)
{
v___y_2490_ = v___x_2452_;
goto v___jp_2489_;
}
else
{
v___y_2490_ = v___x_2502_;
goto v___jp_2489_;
}
v___jp_2489_:
{
if (v___y_2490_ == 0)
{
if (v___x_2450_ == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref_known(v___x_2485_, 1);
lean_inc_ref(v_code_2488_);
lean_inc_ref(v_info_2487_);
lean_inc(v_discr_2451_);
v___x_2491_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2451_, v_info_2487_, v_code_2488_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
v___x_2493_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2486_, v_a_2492_);
v_a_2469_ = v___x_2493_;
goto v___jp_2468_;
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec_ref_known(v_a_2486_, 2);
lean_dec_ref(v_bs_x27_2467_);
lean_dec(v_discr_2451_);
v_a_2494_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2491_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2491_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2486_, 2);
v___y_2475_ = v___x_2485_;
goto v___jp_2474_;
}
}
else
{
lean_dec_ref_known(v_a_2486_, 2);
v___y_2475_ = v___x_2485_;
goto v___jp_2474_;
}
}
}
else
{
lean_dec_ref_known(v_a_2486_, 1);
v___y_2475_ = v___x_2485_;
goto v___jp_2474_;
}
}
else
{
v___y_2475_ = v___x_2485_;
goto v___jp_2474_;
}
v___jp_2468_:
{
size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = ((size_t)1ULL);
v___x_2471_ = lean_usize_add(v_i_2454_, v___x_2470_);
v___x_2472_ = lean_array_uset(v_bs_x27_2467_, v_i_2454_, v_a_2469_);
v_i_2454_ = v___x_2471_;
v_bs_2455_ = v___x_2472_;
goto _start;
}
v___jp_2474_:
{
if (lean_obj_tag(v___y_2475_) == 0)
{
lean_object* v_a_2476_; 
v_a_2476_ = lean_ctor_get(v___y_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___y_2475_, 1);
v_a_2469_ = v_a_2476_;
goto v___jp_2468_;
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_bs_x27_2467_);
lean_dec(v_discr_2451_);
v_a_2477_ = lean_ctor_get(v___y_2475_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___y_2475_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___y_2475_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___y_2475_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2503_, lean_object* v_discr_2504_, lean_object* v___x_2505_, lean_object* v_sz_2506_, lean_object* v_i_2507_, lean_object* v_bs_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
uint8_t v___x_6473__boxed_2515_; uint8_t v___x_6475__boxed_2516_; size_t v_sz_boxed_2517_; size_t v_i_boxed_2518_; lean_object* v_res_2519_; 
v___x_6473__boxed_2515_ = lean_unbox(v___x_2503_);
v___x_6475__boxed_2516_ = lean_unbox(v___x_2505_);
v_sz_boxed_2517_ = lean_unbox_usize(v_sz_2506_);
lean_dec(v_sz_2506_);
v_i_boxed_2518_ = lean_unbox_usize(v_i_2507_);
lean_dec(v_i_2507_);
v_res_2519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6473__boxed_2515_, v_discr_2504_, v___x_6475__boxed_2516_, v_sz_boxed_2517_, v_i_boxed_2518_, v_bs_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2519_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2521_, v_x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_){
_start:
{
uint8_t v_res_2527_; lean_object* v_r_2528_; 
v_res_2527_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2524_, v_x_2525_, v_x_2526_);
lean_dec(v_x_2526_);
lean_dec_ref(v_x_2525_);
v_r_2528_ = lean_box(v_res_2527_);
return v_r_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2529_, lean_object* v_m_2530_, lean_object* v_a_2531_, lean_object* v_fallback_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2530_, v_a_2531_, v_fallback_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2534_, lean_object* v_m_2535_, lean_object* v_a_2536_, lean_object* v_fallback_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2534_, v_m_2535_, v_a_2536_, v_fallback_2537_);
lean_dec(v_fallback_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_m_2535_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2540_, v_x_2541_, v_x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2544_, lean_object* v_x_2545_, size_t v_x_2546_, lean_object* v_x_2547_){
_start:
{
uint8_t v___x_2548_; 
v___x_2548_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2545_, v_x_2546_, v_x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_){
_start:
{
size_t v_x_7024__boxed_2553_; uint8_t v_res_2554_; lean_object* v_r_2555_; 
v_x_7024__boxed_2553_ = lean_unbox_usize(v_x_2551_);
lean_dec(v_x_2551_);
v_res_2554_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2549_, v_x_2550_, v_x_7024__boxed_2553_, v_x_2552_);
lean_dec(v_x_2552_);
lean_dec_ref(v_x_2550_);
v_r_2555_ = lean_box(v_res_2554_);
return v_r_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2556_, lean_object* v_a_2557_, lean_object* v_fallback_2558_, lean_object* v_x_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2557_, v_fallback_2558_, v_x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2561_, lean_object* v_a_2562_, lean_object* v_fallback_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2561_, v_a_2562_, v_fallback_2563_, v_x_2564_);
lean_dec(v_x_2564_);
lean_dec(v_fallback_2563_);
lean_dec(v_a_2562_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2566_, lean_object* v_x_2567_, size_t v_x_2568_, size_t v_x_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2567_, v_x_2568_, v_x_2569_, v_x_2570_, v_x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_){
_start:
{
size_t v_x_7040__boxed_2579_; size_t v_x_7041__boxed_2580_; lean_object* v_res_2581_; 
v_x_7040__boxed_2579_ = lean_unbox_usize(v_x_2575_);
lean_dec(v_x_2575_);
v_x_7041__boxed_2580_ = lean_unbox_usize(v_x_2576_);
lean_dec(v_x_2576_);
v_res_2581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2573_, v_x_2574_, v_x_7040__boxed_2579_, v_x_7041__boxed_2580_, v_x_2577_, v_x_2578_);
return v_res_2581_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2582_, lean_object* v_keys_2583_, lean_object* v_vals_2584_, lean_object* v_heq_2585_, lean_object* v_i_2586_, lean_object* v_k_2587_){
_start:
{
uint8_t v___x_2588_; 
v___x_2588_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2583_, v_i_2586_, v_k_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2589_, lean_object* v_keys_2590_, lean_object* v_vals_2591_, lean_object* v_heq_2592_, lean_object* v_i_2593_, lean_object* v_k_2594_){
_start:
{
uint8_t v_res_2595_; lean_object* v_r_2596_; 
v_res_2595_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2589_, v_keys_2590_, v_vals_2591_, v_heq_2592_, v_i_2593_, v_k_2594_);
lean_dec(v_k_2594_);
lean_dec_ref(v_vals_2591_);
lean_dec_ref(v_keys_2590_);
v_r_2596_ = lean_box(v_res_2595_);
return v_r_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2597_, lean_object* v_n_2598_, lean_object* v_k_2599_, lean_object* v_v_2600_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_2598_, v_k_2599_, v_v_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2602_, size_t v_depth_2603_, lean_object* v_keys_2604_, lean_object* v_vals_2605_, lean_object* v_heq_2606_, lean_object* v_i_2607_, lean_object* v_entries_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2603_, v_keys_2604_, v_vals_2605_, v_i_2607_, v_entries_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2610_, lean_object* v_depth_2611_, lean_object* v_keys_2612_, lean_object* v_vals_2613_, lean_object* v_heq_2614_, lean_object* v_i_2615_, lean_object* v_entries_2616_){
_start:
{
size_t v_depth_boxed_2617_; lean_object* v_res_2618_; 
v_depth_boxed_2617_ = lean_unbox_usize(v_depth_2611_);
lean_dec(v_depth_2611_);
v_res_2618_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_2610_, v_depth_boxed_2617_, v_keys_2612_, v_vals_2613_, v_heq_2614_, v_i_2615_, v_entries_2616_);
lean_dec_ref(v_vals_2613_);
lean_dec_ref(v_keys_2612_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2619_, lean_object* v_x_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2620_, v_x_2621_, v_x_2622_, v_x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_toApplicative_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2698_; 
v___x_2634_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2635_ = l_StateRefT_x27_instMonad___redArg(v___x_2634_);
v_toApplicative_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2635_, 1);
lean_dec(v_unused_2699_);
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2698_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_toApplicative_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2698_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_toFunctor_2640_; lean_object* v_toSeq_2641_; lean_object* v_toSeqLeft_2642_; lean_object* v_toSeqRight_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2696_; 
v_toFunctor_2640_ = lean_ctor_get(v_toApplicative_2636_, 0);
v_toSeq_2641_ = lean_ctor_get(v_toApplicative_2636_, 2);
v_toSeqLeft_2642_ = lean_ctor_get(v_toApplicative_2636_, 3);
v_toSeqRight_2643_ = lean_ctor_get(v_toApplicative_2636_, 4);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_toApplicative_2636_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_toApplicative_2636_, 1);
lean_dec(v_unused_2697_);
v___x_2645_ = v_toApplicative_2636_;
v_isShared_2646_ = v_isSharedCheck_2696_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_toSeqRight_2643_);
lean_inc(v_toSeqLeft_2642_);
lean_inc(v_toSeq_2641_);
lean_inc(v_toFunctor_2640_);
lean_dec(v_toApplicative_2636_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2696_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___f_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; lean_object* v___f_2652_; lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___x_2656_; 
v___f_2647_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2648_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2640_);
v___f_2649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2649_, 0, v_toFunctor_2640_);
v___f_2650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2650_, 0, v_toFunctor_2640_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___f_2649_);
lean_ctor_set(v___x_2651_, 1, v___f_2650_);
v___f_2652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2652_, 0, v_toSeqRight_2643_);
v___f_2653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2653_, 0, v_toSeqLeft_2642_);
v___f_2654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2654_, 0, v_toSeq_2641_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 4, v___f_2652_);
lean_ctor_set(v___x_2645_, 3, v___f_2653_);
lean_ctor_set(v___x_2645_, 2, v___f_2654_);
lean_ctor_set(v___x_2645_, 1, v___f_2647_);
lean_ctor_set(v___x_2645_, 0, v___x_2651_);
v___x_2656_ = v___x_2645_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___f_2647_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v___f_2654_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v___f_2653_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v___f_2652_);
v___x_2656_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2658_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v___f_2648_);
lean_ctor_set(v___x_2638_, 0, v___x_2656_);
v___x_2658_ = v___x_2638_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___f_2648_);
v___x_2658_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v_toApplicative_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2692_; 
v___x_2659_ = l_StateRefT_x27_instMonad___redArg(v___x_2658_);
v_toApplicative_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2659_, 1);
lean_dec(v_unused_2693_);
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2692_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_toApplicative_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2692_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v_toFunctor_2664_; lean_object* v_toSeq_2665_; lean_object* v_toSeqLeft_2666_; lean_object* v_toSeqRight_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2690_; 
v_toFunctor_2664_ = lean_ctor_get(v_toApplicative_2660_, 0);
v_toSeq_2665_ = lean_ctor_get(v_toApplicative_2660_, 2);
v_toSeqLeft_2666_ = lean_ctor_get(v_toApplicative_2660_, 3);
v_toSeqRight_2667_ = lean_ctor_get(v_toApplicative_2660_, 4);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_toApplicative_2660_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v_toApplicative_2660_, 1);
lean_dec(v_unused_2691_);
v___x_2669_ = v_toApplicative_2660_;
v_isShared_2670_ = v_isSharedCheck_2690_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_toSeqRight_2667_);
lean_inc(v_toSeqLeft_2666_);
lean_inc(v_toSeq_2665_);
lean_inc(v_toFunctor_2664_);
lean_dec(v_toApplicative_2660_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2690_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___f_2673_; lean_object* v___f_2674_; lean_object* v___x_2675_; lean_object* v___f_2676_; lean_object* v___f_2677_; lean_object* v___f_2678_; lean_object* v___x_2680_; 
v___f_2671_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2672_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2664_);
v___f_2673_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2673_, 0, v_toFunctor_2664_);
v___f_2674_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2674_, 0, v_toFunctor_2664_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___f_2673_);
lean_ctor_set(v___x_2675_, 1, v___f_2674_);
v___f_2676_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2676_, 0, v_toSeqRight_2667_);
v___f_2677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2677_, 0, v_toSeqLeft_2666_);
v___f_2678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2678_, 0, v_toSeq_2665_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 4, v___f_2676_);
lean_ctor_set(v___x_2669_, 3, v___f_2677_);
lean_ctor_set(v___x_2669_, 2, v___f_2678_);
lean_ctor_set(v___x_2669_, 1, v___f_2671_);
lean_ctor_set(v___x_2669_, 0, v___x_2675_);
v___x_2680_ = v___x_2669_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v___f_2671_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v___f_2678_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v___f_2677_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v___f_2676_);
v___x_2680_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___f_2672_);
lean_ctor_set(v___x_2662_, 0, v___x_2680_);
v___x_2682_ = v___x_2662_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___f_2672_);
v___x_2682_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2508__overap_2686_; lean_object* v___x_2687_; 
v___x_2683_ = l_StateRefT_x27_instMonad___redArg(v___x_2682_);
v___x_2684_ = lean_box(0);
v___x_2685_ = l_instInhabitedOfMonad___redArg(v___x_2683_, v___x_2684_);
v___x_2508__overap_2686_ = lean_panic_fn_borrowed(v___x_2685_, v_msg_2627_);
lean_dec(v___x_2685_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
lean_inc(v___y_2628_);
v___x_2687_ = lean_apply_6(v___x_2508__overap_2686_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, lean_box(0));
return v___x_2687_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
return v_res_2707_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2710_ = lean_unsigned_to_nat(61u);
v___x_2711_ = lean_unsigned_to_nat(304u);
v___x_2712_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2713_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2714_ = l_mkPanicMessageWithDecl(v___x_2713_, v___x_2712_, v___x_2711_, v___x_2710_, v___x_2709_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
switch(lean_obj_tag(v_c_2715_))
{
case 0:
{
lean_object* v_decl_2722_; lean_object* v_value_2723_; 
v_decl_2722_ = lean_ctor_get(v_c_2715_, 0);
v_value_2723_ = lean_ctor_get(v_decl_2722_, 3);
if (lean_obj_tag(v_value_2723_) == 11)
{
lean_object* v_k_2724_; lean_object* v_var_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_inc_ref(v_value_2723_);
v_k_2724_ = lean_ctor_get(v_c_2715_, 1);
lean_inc_ref(v_k_2724_);
lean_dec_ref_known(v_c_2715_, 2);
v_var_2725_ = lean_ctor_get(v_value_2723_, 1);
lean_inc(v_var_2725_);
lean_dec_ref_known(v_value_2723_, 2);
v___x_2726_ = lean_st_ref_take(v_a_2716_);
v___x_2727_ = lean_box(0);
v___x_2728_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2726_, v_var_2725_, v___x_2727_);
v___x_2729_ = lean_st_ref_set(v_a_2716_, v___x_2728_);
v_c_2715_ = v_k_2724_;
goto _start;
}
else
{
lean_object* v_k_2731_; 
v_k_2731_ = lean_ctor_get(v_c_2715_, 1);
lean_inc_ref(v_k_2731_);
lean_dec_ref_known(v_c_2715_, 2);
v_c_2715_ = v_k_2731_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2733_; lean_object* v_k_2734_; lean_object* v_value_2735_; lean_object* v___x_2736_; 
v_decl_2733_ = lean_ctor_get(v_c_2715_, 0);
lean_inc_ref(v_decl_2733_);
v_k_2734_ = lean_ctor_get(v_c_2715_, 1);
lean_inc_ref(v_k_2734_);
lean_dec_ref_known(v_c_2715_, 2);
v_value_2735_ = lean_ctor_get(v_decl_2733_, 4);
lean_inc_ref(v_value_2735_);
lean_dec_ref(v_decl_2733_);
v___x_2736_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2735_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_dec_ref_known(v___x_2736_, 1);
v_c_2715_ = v_k_2734_;
goto _start;
}
else
{
lean_dec_ref(v_k_2734_);
return v___x_2736_;
}
}
case 3:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec_ref_known(v_c_2715_, 2);
v___x_2738_ = lean_box(0);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
return v___x_2739_;
}
case 4:
{
lean_object* v_cases_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2762_; 
v_cases_2740_ = lean_ctor_get(v_c_2715_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_c_2715_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2742_ = v_c_2715_;
v_isShared_2743_ = v_isSharedCheck_2762_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_cases_2740_);
lean_dec(v_c_2715_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2762_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v_alts_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v_alts_2744_ = lean_ctor_get(v_cases_2740_, 3);
lean_inc_ref(v_alts_2744_);
lean_dec_ref(v_cases_2740_);
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_array_get_size(v_alts_2744_);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_nat_dec_lt(v___x_2745_, v___x_2746_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2750_; 
lean_dec_ref(v_alts_2744_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2747_);
v___x_2750_ = v___x_2742_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2747_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
else
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_nat_dec_le(v___x_2746_, v___x_2746_);
if (v___x_2752_ == 0)
{
if (v___x_2748_ == 0)
{
lean_object* v___x_2754_; 
lean_dec_ref(v_alts_2744_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2747_);
v___x_2754_ = v___x_2742_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2747_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
else
{
size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2742_);
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = lean_usize_of_nat(v___x_2746_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2744_, v___x_2756_, v___x_2757_, v___x_2747_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
lean_dec_ref(v_alts_2744_);
return v___x_2758_;
}
}
else
{
size_t v___x_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
lean_del_object(v___x_2742_);
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = lean_usize_of_nat(v___x_2746_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2744_, v___x_2759_, v___x_2760_, v___x_2747_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
lean_dec_ref(v_alts_2744_);
return v___x_2761_;
}
}
}
}
case 5:
{
lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2770_; 
v_isSharedCheck_2770_ = !lean_is_exclusive(v_c_2715_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; 
v_unused_2771_ = lean_ctor_get(v_c_2715_, 0);
lean_dec(v_unused_2771_);
v___x_2764_ = v_c_2715_;
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v_c_2715_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_box(0);
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
case 6:
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v_isSharedCheck_2779_ = !lean_is_exclusive(v_c_2715_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_c_2715_, 0);
lean_dec(v_unused_2780_);
v___x_2773_ = v_c_2715_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_c_2715_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = lean_box(0);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
case 8:
{
lean_object* v_k_2781_; 
v_k_2781_ = lean_ctor_get(v_c_2715_, 3);
lean_inc_ref(v_k_2781_);
lean_dec_ref_known(v_c_2715_, 4);
v_c_2715_ = v_k_2781_;
goto _start;
}
case 9:
{
lean_object* v_k_2783_; 
v_k_2783_ = lean_ctor_get(v_c_2715_, 5);
lean_inc_ref(v_k_2783_);
lean_dec_ref_known(v_c_2715_, 6);
v_c_2715_ = v_k_2783_;
goto _start;
}
default: 
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec_ref(v_c_2715_);
v___x_2785_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2786_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2785_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
return v___x_2786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2787_, size_t v_i_2788_, size_t v_stop_2789_, lean_object* v_b_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___y_2798_; uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_eq(v_i_2788_, v_stop_2789_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_array_uget_borrowed(v_as_2787_, v_i_2788_);
switch(lean_obj_tag(v___x_2805_))
{
case 0:
{
lean_object* v_code_2806_; 
v_code_2806_ = lean_ctor_get(v___x_2805_, 2);
lean_inc_ref(v_code_2806_);
v___y_2798_ = v_code_2806_;
goto v___jp_2797_;
}
case 1:
{
lean_object* v_code_2807_; 
v_code_2807_ = lean_ctor_get(v___x_2805_, 1);
lean_inc_ref(v_code_2807_);
v___y_2798_ = v_code_2807_;
goto v___jp_2797_;
}
default: 
{
lean_object* v_code_2808_; 
v_code_2808_ = lean_ctor_get(v___x_2805_, 0);
lean_inc_ref(v_code_2808_);
v___y_2798_ = v_code_2808_;
goto v___jp_2797_;
}
}
}
else
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_b_2790_);
return v___x_2809_;
}
v___jp_2797_:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2798_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; size_t v___x_2801_; size_t v___x_2802_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = ((size_t)1ULL);
v___x_2802_ = lean_usize_add(v_i_2788_, v___x_2801_);
v_i_2788_ = v___x_2802_;
v_b_2790_ = v_a_2800_;
goto _start;
}
else
{
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_stop_2812_, lean_object* v_b_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
size_t v_i_boxed_2820_; size_t v_stop_boxed_2821_; lean_object* v_res_2822_; 
v_i_boxed_2820_ = lean_unbox_usize(v_i_2811_);
lean_dec(v_i_2811_);
v_stop_boxed_2821_ = lean_unbox_usize(v_stop_2812_);
lean_dec(v_stop_2812_);
v_res_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2810_, v_i_boxed_2820_, v_stop_boxed_2821_, v_b_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v_as_2810_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
return v_res_2830_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2831_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2836_, lean_object* v_v_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
if (lean_obj_tag(v_v_2837_) == 0)
{
lean_object* v_code_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2868_; 
v_code_2844_ = lean_ctor_get(v_v_2837_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_v_2837_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2846_ = v_v_2837_;
v_isShared_2847_ = v_isSharedCheck_2868_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_code_2844_);
lean_dec(v_v_2837_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2868_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; 
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
lean_inc_ref(v___y_2838_);
v___x_2848_ = lean_apply_7(v_f_2836_, v_code_2844_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, lean_box(0));
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2859_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2859_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2859_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v_a_2849_);
v___x_2854_ = v___x_2846_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2856_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2854_);
v___x_2856_ = v___x_2851_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_del_object(v___x_2846_);
v_a_2860_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2848_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2848_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
lean_object* v___x_2869_; 
lean_dec_ref(v_f_2836_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_v_2837_);
return v___x_2869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2870_, lean_object* v_v_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2870_, v_v_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2879_, lean_object* v_f_2880_, lean_object* v_v_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2880_, v_v_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2889_, lean_object* v_f_2890_, lean_object* v_v_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
uint8_t v_pu_boxed_2898_; lean_object* v_res_2899_; 
v_pu_boxed_2898_ = lean_unbox(v_pu_2889_);
v_res_2899_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_2898_, v_f_2890_, v_v_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2899_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_box(0));
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_alreadyFound_2909_; uint8_t v_relaxedReuse_2910_; lean_object* v_ownedness_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; uint8_t v_relaxedReuse_2918_; 
v_relaxedReuse_2918_ = lean_ctor_get_uint8(v___y_2902_, sizeof(void*)*2);
if (v_relaxedReuse_2918_ == 0)
{
lean_object* v_ownedness_2919_; lean_object* v___x_2920_; 
v_ownedness_2919_ = lean_ctor_get(v___y_2902_, 1);
v___x_2920_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v_alreadyFound_2909_ = v___x_2920_;
v_relaxedReuse_2910_ = v_relaxedReuse_2918_;
v_ownedness_2911_ = v_ownedness_2919_;
v___y_2912_ = v___y_2903_;
v___y_2913_ = v___y_2904_;
v___y_2914_ = v___y_2905_;
v___y_2915_ = v___y_2906_;
goto v___jp_2908_;
}
else
{
lean_object* v_ownedness_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_ownedness_2921_ = lean_ctor_get(v___y_2902_, 1);
v___x_2922_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_2923_ = lean_st_mk_ref(v___x_2922_);
lean_inc_ref(v_code_2901_);
v___x_2924_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_2901_, v___x_2923_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v___x_2925_; 
lean_dec_ref_known(v___x_2924_, 1);
v___x_2925_ = lean_st_ref_get(v___x_2923_);
lean_dec(v___x_2923_);
v_alreadyFound_2909_ = v___x_2925_;
v_relaxedReuse_2910_ = v_relaxedReuse_2918_;
v_ownedness_2911_ = v_ownedness_2921_;
v___y_2912_ = v___y_2903_;
v___y_2913_ = v___y_2904_;
v___y_2914_ = v___y_2905_;
v___y_2915_ = v___y_2906_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v___x_2923_);
lean_dec_ref(v_code_2901_);
v_a_2926_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2924_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
v___jp_2908_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_inc_ref(v_ownedness_2911_);
v___x_2916_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2916_, 0, v_alreadyFound_2909_);
lean_ctor_set(v___x_2916_, 1, v_ownedness_2911_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*2, v_relaxedReuse_2910_);
v___x_2917_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_2901_, v___x_2916_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec_ref_known(v___x_2916_, 2);
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_toSignature_2950_; lean_object* v_value_2951_; uint8_t v_recursive_2952_; lean_object* v_inlineAttr_x3f_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2978_; 
v_toSignature_2950_ = lean_ctor_get(v_decl_2943_, 0);
v_value_2951_ = lean_ctor_get(v_decl_2943_, 1);
v_recursive_2952_ = lean_ctor_get_uint8(v_decl_2943_, sizeof(void*)*3);
v_inlineAttr_x3f_2953_ = lean_ctor_get(v_decl_2943_, 2);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_decl_2943_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2955_ = v_decl_2943_;
v_isShared_2956_ = v_isSharedCheck_2978_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_inlineAttr_x3f_2953_);
lean_inc(v_value_2951_);
lean_inc(v_toSignature_2950_);
lean_dec(v_decl_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2978_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___f_2957_; lean_object* v___x_2958_; 
v___f_2957_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_2958_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_2957_, v_value_2951_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2969_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2969_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2969_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v_a_2959_);
v___x_2964_ = v___x_2955_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_toSignature_2950_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_a_2959_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_inlineAttr_x3f_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2968_, sizeof(void*)*3, v_recursive_2952_);
v___x_2964_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2966_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2955_);
lean_dec(v_inlineAttr_x3f_2953_);
lean_dec_ref(v_toSignature_2950_);
v_a_2970_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2958_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2958_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2988_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3021_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3021_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3021_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
uint8_t v_resetReuse_2998_; 
v_resetReuse_2998_ = lean_ctor_get_uint8(v_a_2994_, sizeof(void*)*4 + 2);
lean_dec(v_a_2994_);
if (v_resetReuse_2998_ == 0)
{
lean_object* v___x_3000_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v_decl_2987_);
v___x_3000_ = v___x_2996_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_decl_2987_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
else
{
lean_object* v___x_3002_; 
lean_del_object(v___x_2996_);
lean_inc_ref(v_decl_2987_);
v___x_3002_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc_n(v_a_3003_, 2);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_2987_, v_a_3003_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_3007_ = 0;
lean_inc(v_a_3003_);
v___x_3008_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v_a_3003_);
lean_ctor_set_uint8(v___x_3008_, sizeof(void*)*2, v___x_3007_);
v___x_3009_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3005_, v___x_3008_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
lean_dec_ref_known(v___x_3008_, 2);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3011_, 0, v___x_3006_);
lean_ctor_set(v___x_3011_, 1, v_a_3003_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*2, v_resetReuse_2998_);
v___x_3012_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3010_, v___x_3011_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
lean_dec_ref_known(v___x_3011_, 2);
return v___x_3012_;
}
else
{
lean_dec(v_a_3003_);
return v___x_3009_;
}
}
else
{
lean_dec(v_a_3003_);
return v___x_3004_;
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_decl_2987_);
v_a_3013_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_3002_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3002_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref(v_decl_2987_);
v_a_3022_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2993_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2993_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
return v_res_3036_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3043_ = 2;
v___x_3044_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3045_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3044_, v___x_3043_, v___x_3042_, v___x_3041_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3046_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_unsigned_to_nat(2506150707u);
v___x_3103_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3104_ = l_Lean_Name_num___override(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3107_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3108_ = l_Lean_Name_str___override(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3111_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3112_ = l_Lean_Name_str___override(v___x_3111_, v___x_3110_);
return v___x_3112_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3113_ = lean_unsigned_to_nat(2u);
v___x_3114_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3115_ = l_Lean_Name_num___override(v___x_3114_, v___x_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3118_ = 1;
v___x_3119_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3120_ = l_Lean_registerTraceClass(v___x_3117_, v___x_3118_, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3122_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_LiveVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PropagateBorrow(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ResetReuse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
