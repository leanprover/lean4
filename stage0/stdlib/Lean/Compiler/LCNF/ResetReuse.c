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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_2063_; size_t v___x_2064_; size_t v___x_2065_; 
v___x_2063_ = ((size_t)5ULL);
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_shift_left(v___x_2064_, v___x_2063_);
return v___x_2065_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_2066_; size_t v___x_2067_; size_t v___x_2068_; 
v___x_2066_ = ((size_t)1ULL);
v___x_2067_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__0);
v___x_2068_ = lean_usize_sub(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(lean_object* v_x_2070_, size_t v_x_2071_, size_t v_x_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
lean_object* v_es_2075_; size_t v___x_2076_; size_t v___x_2077_; size_t v___x_2078_; size_t v___x_2079_; lean_object* v_j_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_es_2075_ = lean_ctor_get(v_x_2070_, 0);
v___x_2076_ = ((size_t)5ULL);
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1);
v___x_2079_ = lean_usize_land(v_x_2071_, v___x_2078_);
v_j_2080_ = lean_usize_to_nat(v___x_2079_);
v___x_2081_ = lean_array_get_size(v_es_2075_);
v___x_2082_ = lean_nat_dec_lt(v_j_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec(v_j_2080_);
lean_dec(v_x_2074_);
lean_dec(v_x_2073_);
return v_x_2070_;
}
else
{
lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2119_; 
lean_inc_ref(v_es_2075_);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_x_2070_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_x_2070_, 0);
lean_dec(v_unused_2120_);
v___x_2084_ = v_x_2070_;
v_isShared_2085_ = v_isSharedCheck_2119_;
goto v_resetjp_2083_;
}
else
{
lean_dec(v_x_2070_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2119_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_v_2086_; lean_object* v___x_2087_; lean_object* v_xs_x27_2088_; lean_object* v___y_2090_; 
v_v_2086_ = lean_array_fget(v_es_2075_, v_j_2080_);
v___x_2087_ = lean_box(0);
v_xs_x27_2088_ = lean_array_fset(v_es_2075_, v_j_2080_, v___x_2087_);
switch(lean_obj_tag(v_v_2086_))
{
case 0:
{
lean_object* v_key_2095_; lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2106_; 
v_key_2095_ = lean_ctor_get(v_v_2086_, 0);
v_val_2096_ = lean_ctor_get(v_v_2086_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_v_2086_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2098_ = v_v_2086_;
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_inc(v_key_2095_);
lean_dec(v_v_2086_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2106_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
uint8_t v___x_2100_; 
v___x_2100_ = l_Lean_instBEqFVarId_beq(v_x_2073_, v_key_2095_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_del_object(v___x_2098_);
v___x_2101_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2095_, v_val_2096_, v_x_2073_, v_x_2074_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___y_2090_ = v___x_2102_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2104_; 
lean_dec(v_val_2096_);
lean_dec(v_key_2095_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v_x_2074_);
lean_ctor_set(v___x_2098_, 0, v_x_2073_);
v___x_2104_ = v___x_2098_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_x_2073_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_x_2074_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v___y_2090_ = v___x_2104_;
goto v___jp_2089_;
}
}
}
}
case 1:
{
lean_object* v_node_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_node_2107_ = lean_ctor_get(v_v_2086_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_v_2086_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2109_ = v_v_2086_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_node_2107_);
lean_dec(v_v_2086_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2111_ = lean_usize_shift_right(v_x_2071_, v___x_2076_);
v___x_2112_ = lean_usize_add(v_x_2072_, v___x_2077_);
v___x_2113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_node_2107_, v___x_2111_, v___x_2112_, v_x_2073_, v_x_2074_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2115_ = v___x_2109_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
v___y_2090_ = v___x_2115_;
goto v___jp_2089_;
}
}
}
default: 
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v_x_2073_);
lean_ctor_set(v___x_2118_, 1, v_x_2074_);
v___y_2090_ = v___x_2118_;
goto v___jp_2089_;
}
}
v___jp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_array_fset(v_xs_x27_2088_, v_j_2080_, v___y_2090_);
lean_dec(v_j_2080_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2091_);
v___x_2093_ = v___x_2084_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_object* v_ks_2121_; lean_object* v_vs_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2142_; 
v_ks_2121_ = lean_ctor_get(v_x_2070_, 0);
v_vs_2122_ = lean_ctor_get(v_x_2070_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2070_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2124_ = v_x_2070_;
v_isShared_2125_ = v_isSharedCheck_2142_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_vs_2122_);
lean_inc(v_ks_2121_);
lean_dec(v_x_2070_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2142_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_ks_2121_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_vs_2122_);
v___x_2127_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v_newNode_2128_; uint8_t v___y_2130_; size_t v___x_2136_; uint8_t v___x_2137_; 
v_newNode_2128_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v___x_2127_, v_x_2073_, v_x_2074_);
v___x_2136_ = ((size_t)7ULL);
v___x_2137_ = lean_usize_dec_le(v___x_2136_, v_x_2072_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2138_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2128_);
v___x_2139_ = lean_unsigned_to_nat(4u);
v___x_2140_ = lean_nat_dec_lt(v___x_2138_, v___x_2139_);
lean_dec(v___x_2138_);
v___y_2130_ = v___x_2140_;
goto v___jp_2129_;
}
else
{
v___y_2130_ = v___x_2137_;
goto v___jp_2129_;
}
v___jp_2129_:
{
if (v___y_2130_ == 0)
{
lean_object* v_ks_2131_; lean_object* v_vs_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_ks_2131_ = lean_ctor_get(v_newNode_2128_, 0);
lean_inc_ref(v_ks_2131_);
v_vs_2132_ = lean_ctor_get(v_newNode_2128_, 1);
lean_inc_ref(v_vs_2132_);
lean_dec_ref(v_newNode_2128_);
v___x_2133_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__2);
v___x_2135_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_x_2072_, v_ks_2131_, v_vs_2132_, v___x_2133_, v___x_2134_);
lean_dec_ref(v_vs_2132_);
lean_dec_ref(v_ks_2131_);
return v___x_2135_;
}
else
{
return v_newNode_2128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(size_t v_depth_2143_, lean_object* v_keys_2144_, lean_object* v_vals_2145_, lean_object* v_i_2146_, lean_object* v_entries_2147_){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_array_get_size(v_keys_2144_);
v___x_2149_ = lean_nat_dec_lt(v_i_2146_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_dec(v_i_2146_);
return v_entries_2147_;
}
else
{
lean_object* v_k_2150_; lean_object* v_v_2151_; uint64_t v___x_2152_; size_t v_h_2153_; size_t v___x_2154_; lean_object* v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; size_t v_h_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_k_2150_ = lean_array_fget_borrowed(v_keys_2144_, v_i_2146_);
v_v_2151_ = lean_array_fget_borrowed(v_vals_2145_, v_i_2146_);
v___x_2152_ = l_Lean_instHashableFVarId_hash(v_k_2150_);
v_h_2153_ = lean_uint64_to_usize(v___x_2152_);
v___x_2154_ = ((size_t)5ULL);
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = ((size_t)1ULL);
v___x_2157_ = lean_usize_sub(v_depth_2143_, v___x_2156_);
v___x_2158_ = lean_usize_mul(v___x_2154_, v___x_2157_);
v_h_2159_ = lean_usize_shift_right(v_h_2153_, v___x_2158_);
v___x_2160_ = lean_nat_add(v_i_2146_, v___x_2155_);
lean_dec(v_i_2146_);
lean_inc(v_v_2151_);
lean_inc(v_k_2150_);
v___x_2161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_entries_2147_, v_h_2159_, v_depth_2143_, v_k_2150_, v_v_2151_);
v_i_2146_ = v___x_2160_;
v_entries_2147_ = v___x_2161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_depth_2163_, lean_object* v_keys_2164_, lean_object* v_vals_2165_, lean_object* v_i_2166_, lean_object* v_entries_2167_){
_start:
{
size_t v_depth_boxed_2168_; lean_object* v_res_2169_; 
v_depth_boxed_2168_ = lean_unbox_usize(v_depth_2163_);
lean_dec(v_depth_2163_);
v_res_2169_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_boxed_2168_, v_keys_2164_, v_vals_2165_, v_i_2166_, v_entries_2167_);
lean_dec_ref(v_vals_2165_);
lean_dec_ref(v_keys_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___boxed(lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
size_t v_x_6248__boxed_2175_; size_t v_x_6249__boxed_2176_; lean_object* v_res_2177_; 
v_x_6248__boxed_2175_ = lean_unbox_usize(v_x_2171_);
lean_dec(v_x_2171_);
v_x_6249__boxed_2176_ = lean_unbox_usize(v_x_2172_);
lean_dec(v_x_2172_);
v_res_2177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2170_, v_x_6248__boxed_2175_, v_x_6249__boxed_2176_, v_x_2173_, v_x_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
uint64_t v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2181_ = l_Lean_instHashableFVarId_hash(v_x_2179_);
v___x_2182_ = lean_uint64_to_usize(v___x_2181_);
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2178_, v___x_2182_, v___x_2183_, v_x_2179_, v_x_2180_);
return v___x_2184_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_2185_, lean_object* v_i_2186_, lean_object* v_k_2187_){
_start:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_array_get_size(v_keys_2185_);
v___x_2189_ = lean_nat_dec_lt(v_i_2186_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_dec(v_i_2186_);
return v___x_2189_;
}
else
{
lean_object* v_k_x27_2190_; uint8_t v___x_2191_; 
v_k_x27_2190_ = lean_array_fget_borrowed(v_keys_2185_, v_i_2186_);
v___x_2191_ = l_Lean_instBEqFVarId_beq(v_k_2187_, v_k_x27_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_add(v_i_2186_, v___x_2192_);
lean_dec(v_i_2186_);
v_i_2186_ = v___x_2193_;
goto _start;
}
else
{
lean_dec(v_i_2186_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_2195_, lean_object* v_i_2196_, lean_object* v_k_2197_){
_start:
{
uint8_t v_res_2198_; lean_object* v_r_2199_; 
v_res_2198_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2195_, v_i_2196_, v_k_2197_);
lean_dec(v_k_2197_);
lean_dec_ref(v_keys_2195_);
v_r_2199_ = lean_box(v_res_2198_);
return v_r_2199_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(lean_object* v_x_2200_, size_t v_x_2201_, lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2200_) == 0)
{
lean_object* v_es_2203_; lean_object* v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v_j_2208_; lean_object* v___x_2209_; 
v_es_2203_ = lean_ctor_get(v_x_2200_, 0);
v___x_2204_ = lean_box(2);
v___x_2205_ = ((size_t)5ULL);
v___x_2206_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg___closed__1);
v___x_2207_ = lean_usize_land(v_x_2201_, v___x_2206_);
v_j_2208_ = lean_usize_to_nat(v___x_2207_);
v___x_2209_ = lean_array_get_borrowed(v___x_2204_, v_es_2203_, v_j_2208_);
lean_dec(v_j_2208_);
switch(lean_obj_tag(v___x_2209_))
{
case 0:
{
lean_object* v_key_2210_; uint8_t v___x_2211_; 
v_key_2210_ = lean_ctor_get(v___x_2209_, 0);
v___x_2211_ = l_Lean_instBEqFVarId_beq(v_x_2202_, v_key_2210_);
return v___x_2211_;
}
case 1:
{
lean_object* v_node_2212_; size_t v___x_2213_; 
v_node_2212_ = lean_ctor_get(v___x_2209_, 0);
v___x_2213_ = lean_usize_shift_right(v_x_2201_, v___x_2205_);
v_x_2200_ = v_node_2212_;
v_x_2201_ = v___x_2213_;
goto _start;
}
default: 
{
uint8_t v___x_2215_; 
v___x_2215_ = 0;
return v___x_2215_;
}
}
}
else
{
lean_object* v_ks_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v_ks_2216_ = lean_ctor_get(v_x_2200_, 0);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_ks_2216_, v___x_2217_, v_x_2202_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg___boxed(lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
size_t v_x_6442__boxed_2222_; uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_x_6442__boxed_2222_ = lean_unbox_usize(v_x_2220_);
lean_dec(v_x_2220_);
v_res_2223_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2219_, v_x_6442__boxed_2222_, v_x_2221_);
lean_dec(v_x_2221_);
lean_dec_ref(v_x_2219_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
uint64_t v___x_2227_; size_t v___x_2228_; uint8_t v___x_2229_; 
v___x_2227_ = l_Lean_instHashableFVarId_hash(v_x_2226_);
v___x_2228_ = lean_uint64_to_usize(v___x_2227_);
v___x_2229_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2225_, v___x_2228_, v_x_2226_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg___boxed(lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
uint8_t v_res_2232_; lean_object* v_r_2233_; 
v_res_2232_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2230_, v_x_2231_);
lean_dec(v_x_2231_);
lean_dec_ref(v_x_2230_);
v_r_2233_ = lean_box(v_res_2232_);
return v_r_2233_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2236_ = lean_unsigned_to_nat(59u);
v___x_2237_ = lean_unsigned_to_nat(281u);
v___x_2238_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__0));
v___x_2239_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2240_ = l_mkPanicMessageWithDecl(v___x_2239_, v___x_2238_, v___x_2237_, v___x_2236_, v___x_2235_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(lean_object* v_c_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
switch(lean_obj_tag(v_c_2241_))
{
case 0:
{
lean_object* v_decl_2248_; lean_object* v_k_2249_; lean_object* v___x_2250_; 
v_decl_2248_ = lean_ctor_get(v_c_2241_, 0);
v_k_2249_ = lean_ctor_get(v_c_2241_, 1);
lean_inc_ref(v_k_2249_);
v___x_2250_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2249_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2273_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2273_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2273_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
size_t v___x_2255_; size_t v___x_2256_; uint8_t v___x_2257_; 
v___x_2255_ = lean_ptr_addr(v_k_2249_);
v___x_2256_ = lean_ptr_addr(v_a_2251_);
v___x_2257_ = lean_usize_dec_eq(v___x_2255_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2267_; 
lean_inc_ref(v_decl_2248_);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_c_2241_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; lean_object* v_unused_2269_; 
v_unused_2268_ = lean_ctor_get(v_c_2241_, 1);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_c_2241_, 0);
lean_dec(v_unused_2269_);
v___x_2259_ = v_c_2241_;
v_isShared_2260_ = v_isSharedCheck_2267_;
goto v_resetjp_2258_;
}
else
{
lean_dec(v_c_2241_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2267_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v_a_2251_);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_decl_2248_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_a_2251_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2262_);
v___x_2264_ = v___x_2253_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v___x_2271_; 
lean_dec(v_a_2251_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v_c_2241_);
v___x_2271_ = v___x_2253_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_c_2241_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2241_, 2);
return v___x_2250_;
}
}
case 2:
{
lean_object* v_decl_2274_; lean_object* v_k_2275_; lean_object* v_params_2276_; lean_object* v_type_2277_; lean_object* v_value_2278_; lean_object* v___x_2279_; 
v_decl_2274_ = lean_ctor_get(v_c_2241_, 0);
v_k_2275_ = lean_ctor_get(v_c_2241_, 1);
v_params_2276_ = lean_ctor_get(v_decl_2274_, 2);
v_type_2277_ = lean_ctor_get(v_decl_2274_, 3);
v_value_2278_ = lean_ctor_get(v_decl_2274_, 4);
lean_inc_ref(v_value_2278_);
v___x_2279_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_value_2278_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = 1;
lean_inc_ref(v_params_2276_);
lean_inc_ref(v_type_2277_);
lean_inc_ref(v_decl_2274_);
v___x_2282_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2281_, v_decl_2274_, v_type_2277_, v_params_2276_, v_a_2280_, v_a_2244_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
lean_inc_ref(v_k_2275_);
v___x_2284_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2275_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2312_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2312_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2312_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
uint8_t v___y_2290_; size_t v___x_2306_; size_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2306_ = lean_ptr_addr(v_k_2275_);
v___x_2307_ = lean_ptr_addr(v_a_2285_);
v___x_2308_ = lean_usize_dec_eq(v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
v___y_2290_ = v___x_2308_;
goto v___jp_2289_;
}
else
{
size_t v___x_2309_; size_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2309_ = lean_ptr_addr(v_decl_2274_);
v___x_2310_ = lean_ptr_addr(v_a_2283_);
v___x_2311_ = lean_usize_dec_eq(v___x_2309_, v___x_2310_);
v___y_2290_ = v___x_2311_;
goto v___jp_2289_;
}
v___jp_2289_:
{
if (v___y_2290_ == 0)
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2300_; 
v_isSharedCheck_2300_ = !lean_is_exclusive(v_c_2241_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; lean_object* v_unused_2302_; 
v_unused_2301_ = lean_ctor_get(v_c_2241_, 1);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_c_2241_, 0);
lean_dec(v_unused_2302_);
v___x_2292_ = v_c_2241_;
v_isShared_2293_ = v_isSharedCheck_2300_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_c_2241_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2300_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v_a_2285_);
lean_ctor_set(v___x_2292_, 0, v_a_2283_);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2283_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2285_);
v___x_2295_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2297_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2295_);
v___x_2297_ = v___x_2287_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v___x_2304_; 
lean_dec(v_a_2285_);
lean_dec(v_a_2283_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_c_2241_);
v___x_2304_ = v___x_2287_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_c_2241_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_dec(v_a_2283_);
lean_dec_ref_known(v_c_2241_, 2);
return v___x_2284_;
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref_known(v_c_2241_, 2);
v_a_2313_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2282_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2282_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2241_, 2);
return v___x_2279_;
}
}
case 3:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_c_2241_);
return v___x_2321_;
}
case 4:
{
lean_object* v_cases_2322_; lean_object* v_typeName_2323_; lean_object* v_resultType_2324_; lean_object* v_discr_2325_; lean_object* v_alts_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2379_; 
v_cases_2322_ = lean_ctor_get(v_c_2241_, 0);
lean_inc_ref(v_cases_2322_);
v_typeName_2323_ = lean_ctor_get(v_cases_2322_, 0);
v_resultType_2324_ = lean_ctor_get(v_cases_2322_, 1);
v_discr_2325_ = lean_ctor_get(v_cases_2322_, 2);
v_alts_2326_ = lean_ctor_get(v_cases_2322_, 3);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_cases_2322_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2328_ = v_cases_2322_;
v_isShared_2329_ = v_isSharedCheck_2379_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_alts_2326_);
lean_inc(v_discr_2325_);
lean_inc(v_resultType_2324_);
lean_inc(v_typeName_2323_);
lean_dec(v_cases_2322_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2379_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_alreadyFound_2330_; uint8_t v_relaxedReuse_2331_; lean_object* v_ownedness_2332_; uint8_t v___x_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; uint8_t v___x_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; size_t v_sz_2343_; size_t v___x_2344_; lean_object* v___x_2345_; 
v_alreadyFound_2330_ = lean_ctor_get(v_a_2242_, 0);
v_relaxedReuse_2331_ = lean_ctor_get_uint8(v_a_2242_, sizeof(void*)*2);
v_ownedness_2332_ = lean_ctor_get(v_a_2242_, 1);
v___x_2333_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_alreadyFound_2330_, v_discr_2325_);
v___x_2334_ = 0;
v___x_2335_ = lean_box(v___x_2334_);
v___x_2336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_ownedness_2332_, v_discr_2325_, v___x_2335_);
lean_dec(v___x_2335_);
v___x_2337_ = 1;
v___x_2338_ = lean_unbox(v___x_2336_);
lean_dec(v___x_2336_);
v___x_2339_ = l_Lean_Compiler_LCNF_instBEqOwnedness_beq(v___x_2338_, v___x_2337_);
v___x_2340_ = lean_box(0);
lean_inc_n(v_discr_2325_, 2);
lean_inc_ref(v_alreadyFound_2330_);
v___x_2341_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_alreadyFound_2330_, v_discr_2325_, v___x_2340_);
lean_inc_ref(v_ownedness_2332_);
v___x_2342_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v_ownedness_2332_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*2, v_relaxedReuse_2331_);
v_sz_2343_ = lean_array_size(v_alts_2326_);
v___x_2344_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2326_);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_2339_, v_discr_2325_, v___x_2333_, v_sz_2343_, v___x_2344_, v_alts_2326_, v___x_2342_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
lean_dec_ref_known(v___x_2342_, 2);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2370_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2370_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2370_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
size_t v___x_2350_; size_t v___x_2351_; uint8_t v___x_2352_; 
v___x_2350_ = lean_ptr_addr(v_alts_2326_);
lean_dec_ref(v_alts_2326_);
v___x_2351_ = lean_ptr_addr(v_a_2346_);
v___x_2352_ = lean_usize_dec_eq(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2365_; 
v_isSharedCheck_2365_ = !lean_is_exclusive(v_c_2241_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_c_2241_, 0);
lean_dec(v_unused_2366_);
v___x_2354_ = v_c_2241_;
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v_c_2241_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 3, v_a_2346_);
v___x_2357_ = v___x_2328_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_typeName_2323_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_resultType_2324_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_discr_2325_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_a_2346_);
v___x_2357_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2359_);
v___x_2361_ = v___x_2348_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
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
else
{
lean_object* v___x_2368_; 
lean_dec(v_a_2346_);
lean_del_object(v___x_2328_);
lean_dec(v_discr_2325_);
lean_dec_ref(v_resultType_2324_);
lean_dec(v_typeName_2323_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v_c_2241_);
v___x_2368_ = v___x_2348_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_c_2241_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_del_object(v___x_2328_);
lean_dec_ref(v_alts_2326_);
lean_dec(v_discr_2325_);
lean_dec_ref(v_resultType_2324_);
lean_dec(v_typeName_2323_);
lean_dec_ref_known(v_c_2241_, 1);
v_a_2371_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2345_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2345_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
case 5:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v_c_2241_);
return v___x_2380_;
}
case 6:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_c_2241_);
return v___x_2381_;
}
case 8:
{
lean_object* v_fvarId_2382_; lean_object* v_i_2383_; lean_object* v_y_2384_; lean_object* v_k_2385_; lean_object* v___x_2386_; 
v_fvarId_2382_ = lean_ctor_get(v_c_2241_, 0);
v_i_2383_ = lean_ctor_get(v_c_2241_, 1);
v_y_2384_ = lean_ctor_get(v_c_2241_, 2);
v_k_2385_ = lean_ctor_get(v_c_2241_, 3);
lean_inc_ref(v_k_2385_);
v___x_2386_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2385_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2411_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2411_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2411_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
size_t v___x_2391_; size_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2391_ = lean_ptr_addr(v_k_2385_);
v___x_2392_ = lean_ptr_addr(v_a_2387_);
v___x_2393_ = lean_usize_dec_eq(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2403_; 
lean_inc(v_y_2384_);
lean_inc(v_i_2383_);
lean_inc(v_fvarId_2382_);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_c_2241_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; lean_object* v_unused_2405_; lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2404_ = lean_ctor_get(v_c_2241_, 3);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_c_2241_, 2);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_c_2241_, 1);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_c_2241_, 0);
lean_dec(v_unused_2407_);
v___x_2395_ = v_c_2241_;
v_isShared_2396_ = v_isSharedCheck_2403_;
goto v_resetjp_2394_;
}
else
{
lean_dec(v_c_2241_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2403_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 3, v_a_2387_);
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_fvarId_2382_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_i_2383_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_y_2384_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v_a_2387_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2398_);
v___x_2400_ = v___x_2389_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v___x_2409_; 
lean_dec(v_a_2387_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_c_2241_);
v___x_2409_ = v___x_2389_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_c_2241_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2241_, 4);
return v___x_2386_;
}
}
case 9:
{
lean_object* v_fvarId_2412_; lean_object* v_i_2413_; lean_object* v_offset_2414_; lean_object* v_y_2415_; lean_object* v_ty_2416_; lean_object* v_k_2417_; lean_object* v___x_2418_; 
v_fvarId_2412_ = lean_ctor_get(v_c_2241_, 0);
v_i_2413_ = lean_ctor_get(v_c_2241_, 1);
v_offset_2414_ = lean_ctor_get(v_c_2241_, 2);
v_y_2415_ = lean_ctor_get(v_c_2241_, 3);
v_ty_2416_ = lean_ctor_get(v_c_2241_, 4);
v_k_2417_ = lean_ctor_get(v_c_2241_, 5);
lean_inc_ref(v_k_2417_);
v___x_2418_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_k_2417_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2445_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2445_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2445_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
size_t v___x_2423_; size_t v___x_2424_; uint8_t v___x_2425_; 
v___x_2423_ = lean_ptr_addr(v_k_2417_);
v___x_2424_ = lean_ptr_addr(v_a_2419_);
v___x_2425_ = lean_usize_dec_eq(v___x_2423_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2435_; 
lean_inc_ref(v_ty_2416_);
lean_inc(v_y_2415_);
lean_inc(v_offset_2414_);
lean_inc(v_i_2413_);
lean_inc(v_fvarId_2412_);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_c_2241_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; lean_object* v_unused_2437_; lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; lean_object* v_unused_2441_; 
v_unused_2436_ = lean_ctor_get(v_c_2241_, 5);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_c_2241_, 4);
lean_dec(v_unused_2437_);
v_unused_2438_ = lean_ctor_get(v_c_2241_, 3);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_c_2241_, 2);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_c_2241_, 1);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_c_2241_, 0);
lean_dec(v_unused_2441_);
v___x_2427_ = v_c_2241_;
v_isShared_2428_ = v_isSharedCheck_2435_;
goto v_resetjp_2426_;
}
else
{
lean_dec(v_c_2241_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2435_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 5, v_a_2419_);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_fvarId_2412_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_i_2413_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_offset_2414_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_y_2415_);
lean_ctor_set(v_reuseFailAlloc_2434_, 4, v_ty_2416_);
lean_ctor_set(v_reuseFailAlloc_2434_, 5, v_a_2419_);
v___x_2430_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2430_);
v___x_2432_ = v___x_2421_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v___x_2443_; 
lean_dec(v_a_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_c_2241_);
v___x_2443_ = v___x_2421_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_c_2241_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_2241_, 6);
return v___x_2418_;
}
}
default: 
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec_ref(v_c_2241_);
v___x_2446_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___closed__1);
v___x_2447_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__4(v___x_2446_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed(lean_object* v_c_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_c_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_a_2449_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(uint8_t v___x_2456_, lean_object* v_discr_2457_, uint8_t v___x_2458_, size_t v_sz_2459_, size_t v_i_2460_, lean_object* v_bs_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_usize_dec_lt(v_i_2460_, v_sz_2459_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; 
lean_dec(v_discr_2457_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_bs_2461_);
return v___x_2469_;
}
else
{
lean_object* v___f_2470_; lean_object* v_v_2471_; lean_object* v___x_2472_; lean_object* v_bs_x27_2473_; lean_object* v_a_2475_; lean_object* v___y_2481_; lean_object* v___x_2491_; 
v___f_2470_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse___boxed), 7, 0);
v_v_2471_ = lean_array_uget(v_bs_2461_, v_i_2460_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v_bs_x27_2473_ = lean_array_uset(v_bs_2461_, v_i_2460_, v___x_2472_);
v___x_2491_ = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D_go_spec__0___redArg(v_v_2471_, v___f_2470_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
if (lean_obj_tag(v_a_2492_) == 1)
{
lean_object* v_info_2493_; lean_object* v_code_2494_; uint8_t v___y_2496_; uint8_t v___x_2508_; 
v_info_2493_ = lean_ctor_get(v_a_2492_, 0);
v_code_2494_ = lean_ctor_get(v_a_2492_, 1);
v___x_2508_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_info_2493_);
if (v___x_2508_ == 0)
{
v___y_2496_ = v___x_2458_;
goto v___jp_2495_;
}
else
{
v___y_2496_ = v___x_2508_;
goto v___jp_2495_;
}
v___jp_2495_:
{
if (v___y_2496_ == 0)
{
if (v___x_2456_ == 0)
{
lean_object* v___x_2497_; 
lean_dec_ref_known(v___x_2491_, 1);
lean_inc_ref(v_code_2494_);
lean_inc_ref(v_info_2493_);
lean_inc(v_discr_2457_);
v___x_2497_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_D(v_discr_2457_, v_info_2493_, v_code_2494_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2492_, v_a_2498_);
v_a_2475_ = v___x_2499_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref_known(v_a_2492_, 2);
lean_dec_ref(v_bs_x27_2473_);
lean_dec(v_discr_2457_);
v_a_2500_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2497_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2497_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2492_, 2);
v___y_2481_ = v___x_2491_;
goto v___jp_2480_;
}
}
else
{
lean_dec_ref_known(v_a_2492_, 2);
v___y_2481_ = v___x_2491_;
goto v___jp_2480_;
}
}
}
else
{
lean_dec_ref_known(v_a_2492_, 1);
v___y_2481_ = v___x_2491_;
goto v___jp_2480_;
}
}
else
{
v___y_2481_ = v___x_2491_;
goto v___jp_2480_;
}
v___jp_2474_:
{
size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((size_t)1ULL);
v___x_2477_ = lean_usize_add(v_i_2460_, v___x_2476_);
v___x_2478_ = lean_array_uset(v_bs_x27_2473_, v_i_2460_, v_a_2475_);
v_i_2460_ = v___x_2477_;
v_bs_2461_ = v___x_2478_;
goto _start;
}
v___jp_2480_:
{
if (lean_obj_tag(v___y_2481_) == 0)
{
lean_object* v_a_2482_; 
v_a_2482_ = lean_ctor_get(v___y_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___y_2481_, 1);
v_a_2475_ = v_a_2482_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v_bs_x27_2473_);
lean_dec(v_discr_2457_);
v_a_2483_ = lean_ctor_get(v___y_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___y_2481_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___y_2481_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___y_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3___boxed(lean_object* v___x_2509_, lean_object* v_discr_2510_, lean_object* v___x_2511_, lean_object* v_sz_2512_, lean_object* v_i_2513_, lean_object* v_bs_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
uint8_t v___x_6505__boxed_2521_; uint8_t v___x_6507__boxed_2522_; size_t v_sz_boxed_2523_; size_t v_i_boxed_2524_; lean_object* v_res_2525_; 
v___x_6505__boxed_2521_ = lean_unbox(v___x_2509_);
v___x_6507__boxed_2522_ = lean_unbox(v___x_2511_);
v_sz_boxed_2523_ = lean_unbox_usize(v_sz_2512_);
lean_dec(v_sz_2512_);
v_i_boxed_2524_ = lean_unbox_usize(v_i_2513_);
lean_dec(v_i_2513_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__3(v___x_6505__boxed_2521_, v_discr_2510_, v___x_6507__boxed_2522_, v_sz_boxed_2523_, v_i_boxed_2524_, v_bs_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v___y_2515_);
return v_res_2525_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(lean_object* v_00_u03b2_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___redArg(v_x_2527_, v_x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0___boxed(lean_object* v_00_u03b2_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
uint8_t v_res_2533_; lean_object* v_r_2534_; 
v_res_2533_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0(v_00_u03b2_2530_, v_x_2531_, v_x_2532_);
lean_dec(v_x_2532_);
lean_dec_ref(v_x_2531_);
v_r_2534_ = lean_box(v_res_2533_);
return v_r_2534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(lean_object* v_00_u03b2_2535_, lean_object* v_m_2536_, lean_object* v_a_2537_, lean_object* v_fallback_2538_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___redArg(v_m_2536_, v_a_2537_, v_fallback_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1___boxed(lean_object* v_00_u03b2_2540_, lean_object* v_m_2541_, lean_object* v_a_2542_, lean_object* v_fallback_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1(v_00_u03b2_2540_, v_m_2541_, v_a_2542_, v_fallback_2543_);
lean_dec(v_fallback_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_m_2541_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2(lean_object* v_00_u03b2_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v_x_2546_, v_x_2547_, v_x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(lean_object* v_00_u03b2_2550_, lean_object* v_x_2551_, size_t v_x_2552_, lean_object* v_x_2553_){
_start:
{
uint8_t v___x_2554_; 
v___x_2554_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___redArg(v_x_2551_, v_x_2552_, v_x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
size_t v_x_7056__boxed_2559_; uint8_t v_res_2560_; lean_object* v_r_2561_; 
v_x_7056__boxed_2559_ = lean_unbox_usize(v_x_2557_);
lean_dec(v_x_2557_);
v_res_2560_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0(v_00_u03b2_2555_, v_x_2556_, v_x_7056__boxed_2559_, v_x_2558_);
lean_dec(v_x_2558_);
lean_dec_ref(v_x_2556_);
v_r_2561_ = lean_box(v_res_2560_);
return v_r_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(lean_object* v_00_u03b2_2562_, lean_object* v_a_2563_, lean_object* v_fallback_2564_, lean_object* v_x_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___redArg(v_a_2563_, v_fallback_2564_, v_x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2567_, lean_object* v_a_2568_, lean_object* v_fallback_2569_, lean_object* v_x_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__1_spec__2(v_00_u03b2_2567_, v_a_2568_, v_fallback_2569_, v_x_2570_);
lean_dec(v_x_2570_);
lean_dec(v_fallback_2569_);
lean_dec(v_a_2568_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(lean_object* v_00_u03b2_2572_, lean_object* v_x_2573_, size_t v_x_2574_, size_t v_x_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___redArg(v_x_2573_, v_x_2574_, v_x_2575_, v_x_2576_, v_x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_, lean_object* v_x_2584_){
_start:
{
size_t v_x_7072__boxed_2585_; size_t v_x_7073__boxed_2586_; lean_object* v_res_2587_; 
v_x_7072__boxed_2585_ = lean_unbox_usize(v_x_2581_);
lean_dec(v_x_2581_);
v_x_7073__boxed_2586_ = lean_unbox_usize(v_x_2582_);
lean_dec(v_x_2582_);
v_res_2587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4(v_00_u03b2_2579_, v_x_2580_, v_x_7072__boxed_2585_, v_x_7073__boxed_2586_, v_x_2583_, v_x_2584_);
return v_res_2587_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2588_, lean_object* v_keys_2589_, lean_object* v_vals_2590_, lean_object* v_heq_2591_, lean_object* v_i_2592_, lean_object* v_k_2593_){
_start:
{
uint8_t v___x_2594_; 
v___x_2594_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___redArg(v_keys_2589_, v_i_2592_, v_k_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2595_, lean_object* v_keys_2596_, lean_object* v_vals_2597_, lean_object* v_heq_2598_, lean_object* v_i_2599_, lean_object* v_k_2600_){
_start:
{
uint8_t v_res_2601_; lean_object* v_r_2602_; 
v_res_2601_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__0_spec__0_spec__2(v_00_u03b2_2595_, v_keys_2596_, v_vals_2597_, v_heq_2598_, v_i_2599_, v_k_2600_);
lean_dec(v_k_2600_);
lean_dec_ref(v_vals_2597_);
lean_dec_ref(v_keys_2596_);
v_r_2602_ = lean_box(v_res_2601_);
return v_r_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_2603_, lean_object* v_n_2604_, lean_object* v_k_2605_, lean_object* v_v_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7___redArg(v_n_2604_, v_k_2605_, v_v_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_2608_, size_t v_depth_2609_, lean_object* v_keys_2610_, lean_object* v_vals_2611_, lean_object* v_heq_2612_, lean_object* v_i_2613_, lean_object* v_entries_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___redArg(v_depth_2609_, v_keys_2610_, v_vals_2611_, v_i_2613_, v_entries_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2616_, lean_object* v_depth_2617_, lean_object* v_keys_2618_, lean_object* v_vals_2619_, lean_object* v_heq_2620_, lean_object* v_i_2621_, lean_object* v_entries_2622_){
_start:
{
size_t v_depth_boxed_2623_; lean_object* v_res_2624_; 
v_depth_boxed_2623_ = lean_unbox_usize(v_depth_2617_);
lean_dec(v_depth_2617_);
v_res_2624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__8(v_00_u03b2_2616_, v_depth_boxed_2623_, v_keys_2618_, v_vals_2619_, v_heq_2620_, v_i_2621_, v_entries_2622_);
lean_dec_ref(v_vals_2619_);
lean_dec_ref(v_keys_2618_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2_spec__4_spec__7_spec__9___redArg(v_x_2626_, v_x_2627_, v_x_2628_, v_x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(lean_object* v_msg_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_toApplicative_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2704_; 
v___x_2640_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__0);
v___x_2641_ = l_StateRefT_x27_instMonad___redArg(v___x_2640_);
v_toApplicative_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2641_, 1);
lean_dec(v_unused_2705_);
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2704_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_toApplicative_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2704_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_toFunctor_2646_; lean_object* v_toSeq_2647_; lean_object* v_toSeqLeft_2648_; lean_object* v_toSeqRight_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2702_; 
v_toFunctor_2646_ = lean_ctor_get(v_toApplicative_2642_, 0);
v_toSeq_2647_ = lean_ctor_get(v_toApplicative_2642_, 2);
v_toSeqLeft_2648_ = lean_ctor_get(v_toApplicative_2642_, 3);
v_toSeqRight_2649_ = lean_ctor_get(v_toApplicative_2642_, 4);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_toApplicative_2642_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v_toApplicative_2642_, 1);
lean_dec(v_unused_2703_);
v___x_2651_ = v_toApplicative_2642_;
v_isShared_2652_ = v_isSharedCheck_2702_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_toSeqRight_2649_);
lean_inc(v_toSeqLeft_2648_);
lean_inc(v_toSeq_2647_);
lean_inc(v_toFunctor_2646_);
lean_dec(v_toApplicative_2642_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2702_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___f_2653_; lean_object* v___f_2654_; lean_object* v___f_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v___f_2658_; lean_object* v___f_2659_; lean_object* v___f_2660_; lean_object* v___x_2662_; 
v___f_2653_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__1));
v___f_2654_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go_spec__3___closed__2));
lean_inc_ref(v_toFunctor_2646_);
v___f_2655_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2655_, 0, v_toFunctor_2646_);
v___f_2656_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2656_, 0, v_toFunctor_2646_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___f_2655_);
lean_ctor_set(v___x_2657_, 1, v___f_2656_);
v___f_2658_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2658_, 0, v_toSeqRight_2649_);
v___f_2659_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2659_, 0, v_toSeqLeft_2648_);
v___f_2660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2660_, 0, v_toSeq_2647_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 4, v___f_2658_);
lean_ctor_set(v___x_2651_, 3, v___f_2659_);
lean_ctor_set(v___x_2651_, 2, v___f_2660_);
lean_ctor_set(v___x_2651_, 1, v___f_2653_);
lean_ctor_set(v___x_2651_, 0, v___x_2657_);
v___x_2662_ = v___x_2651_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___f_2653_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v___f_2660_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v___f_2659_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v___f_2658_);
v___x_2662_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2664_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___f_2654_);
lean_ctor_set(v___x_2644_, 0, v___x_2662_);
v___x_2664_ = v___x_2644_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___f_2654_);
v___x_2664_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v_toApplicative_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2698_; 
v___x_2665_ = l_StateRefT_x27_instMonad___redArg(v___x_2664_);
v_toApplicative_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v___x_2665_, 1);
lean_dec(v_unused_2699_);
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2698_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_toApplicative_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2698_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_toFunctor_2670_; lean_object* v_toSeq_2671_; lean_object* v_toSeqLeft_2672_; lean_object* v_toSeqRight_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2696_; 
v_toFunctor_2670_ = lean_ctor_get(v_toApplicative_2666_, 0);
v_toSeq_2671_ = lean_ctor_get(v_toApplicative_2666_, 2);
v_toSeqLeft_2672_ = lean_ctor_get(v_toApplicative_2666_, 3);
v_toSeqRight_2673_ = lean_ctor_get(v_toApplicative_2666_, 4);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_toApplicative_2666_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_toApplicative_2666_, 1);
lean_dec(v_unused_2697_);
v___x_2675_ = v_toApplicative_2666_;
v_isShared_2676_ = v_isSharedCheck_2696_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_toSeqRight_2673_);
lean_inc(v_toSeqLeft_2672_);
lean_inc(v_toSeq_2671_);
lean_inc(v_toFunctor_2670_);
lean_dec(v_toApplicative_2666_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2696_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___f_2677_; lean_object* v___f_2678_; lean_object* v___f_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; lean_object* v___f_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___x_2686_; 
v___f_2677_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__0));
v___f_2678_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___closed__1));
lean_inc_ref(v_toFunctor_2670_);
v___f_2679_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2679_, 0, v_toFunctor_2670_);
v___f_2680_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2680_, 0, v_toFunctor_2670_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___f_2679_);
lean_ctor_set(v___x_2681_, 1, v___f_2680_);
v___f_2682_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2682_, 0, v_toSeqRight_2673_);
v___f_2683_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2683_, 0, v_toSeqLeft_2672_);
v___f_2684_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2684_, 0, v_toSeq_2671_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 4, v___f_2682_);
lean_ctor_set(v___x_2675_, 3, v___f_2683_);
lean_ctor_set(v___x_2675_, 2, v___f_2684_);
lean_ctor_set(v___x_2675_, 1, v___f_2677_);
lean_ctor_set(v___x_2675_, 0, v___x_2681_);
v___x_2686_ = v___x_2675_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___f_2677_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v___f_2684_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v___f_2683_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v___f_2682_);
v___x_2686_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2688_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___f_2678_);
lean_ctor_set(v___x_2668_, 0, v___x_2686_);
v___x_2688_ = v___x_2668_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___f_2678_);
v___x_2688_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2508__overap_2692_; lean_object* v___x_2693_; 
v___x_2689_ = l_StateRefT_x27_instMonad___redArg(v___x_2688_);
v___x_2690_ = lean_box(0);
v___x_2691_ = l_instInhabitedOfMonad___redArg(v___x_2689_, v___x_2690_);
v___x_2508__overap_2692_ = lean_panic_fn_borrowed(v___x_2691_, v_msg_2633_);
lean_dec(v___x_2691_);
lean_inc(v___y_2638_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v___y_2634_);
v___x_2693_ = lean_apply_6(v___x_2508__overap_2692_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, lean_box(0));
return v___x_2693_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1___boxed(lean_object* v_msg_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v_msg_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
return v_res_2713_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__2));
v___x_2716_ = lean_unsigned_to_nat(61u);
v___x_2717_ = lean_unsigned_to_nat(304u);
v___x_2718_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__0));
v___x_2719_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_S_go___closed__4));
v___x_2720_ = l_mkPanicMessageWithDecl(v___x_2719_, v___x_2718_, v___x_2717_, v___x_2716_, v___x_2715_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(lean_object* v_c_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
switch(lean_obj_tag(v_c_2721_))
{
case 0:
{
lean_object* v_decl_2728_; lean_object* v_value_2729_; 
v_decl_2728_ = lean_ctor_get(v_c_2721_, 0);
v_value_2729_ = lean_ctor_get(v_decl_2728_, 3);
if (lean_obj_tag(v_value_2729_) == 11)
{
lean_object* v_k_2730_; lean_object* v_var_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_inc_ref(v_value_2729_);
v_k_2730_ = lean_ctor_get(v_c_2721_, 1);
lean_inc_ref(v_k_2730_);
lean_dec_ref_known(v_c_2721_, 2);
v_var_2731_ = lean_ctor_get(v_value_2729_, 1);
lean_inc(v_var_2731_);
lean_dec_ref_known(v_value_2729_, 2);
v___x_2732_ = lean_st_ref_take(v_a_2722_);
v___x_2733_ = lean_box(0);
v___x_2734_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse_spec__2___redArg(v___x_2732_, v_var_2731_, v___x_2733_);
v___x_2735_ = lean_st_ref_set(v_a_2722_, v___x_2734_);
v_c_2721_ = v_k_2730_;
goto _start;
}
else
{
lean_object* v_k_2737_; 
v_k_2737_ = lean_ctor_get(v_c_2721_, 1);
lean_inc_ref(v_k_2737_);
lean_dec_ref_known(v_c_2721_, 2);
v_c_2721_ = v_k_2737_;
goto _start;
}
}
case 2:
{
lean_object* v_decl_2739_; lean_object* v_k_2740_; lean_object* v_value_2741_; lean_object* v___x_2742_; 
v_decl_2739_ = lean_ctor_get(v_c_2721_, 0);
lean_inc_ref(v_decl_2739_);
v_k_2740_ = lean_ctor_get(v_c_2721_, 1);
lean_inc_ref(v_k_2740_);
lean_dec_ref_known(v_c_2721_, 2);
v_value_2741_ = lean_ctor_get(v_decl_2739_, 4);
lean_inc_ref(v_value_2741_);
lean_dec_ref(v_decl_2739_);
v___x_2742_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_value_2741_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_dec_ref_known(v___x_2742_, 1);
v_c_2721_ = v_k_2740_;
goto _start;
}
else
{
lean_dec_ref(v_k_2740_);
return v___x_2742_;
}
}
case 3:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec_ref_known(v_c_2721_, 2);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
case 4:
{
lean_object* v_cases_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2768_; 
v_cases_2746_ = lean_ctor_get(v_c_2721_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_c_2721_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2748_ = v_c_2721_;
v_isShared_2749_ = v_isSharedCheck_2768_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_cases_2746_);
lean_dec(v_c_2721_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2768_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_alts_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_alts_2750_ = lean_ctor_get(v_cases_2746_, 3);
lean_inc_ref(v_alts_2750_);
lean_dec_ref(v_cases_2746_);
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = lean_array_get_size(v_alts_2750_);
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_nat_dec_lt(v___x_2751_, v___x_2752_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref(v_alts_2750_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2753_);
v___x_2756_ = v___x_2748_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2753_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
else
{
uint8_t v___x_2758_; 
v___x_2758_ = lean_nat_dec_le(v___x_2752_, v___x_2752_);
if (v___x_2758_ == 0)
{
if (v___x_2754_ == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v_alts_2750_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2753_);
v___x_2760_ = v___x_2748_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2753_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
else
{
size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
lean_del_object(v___x_2748_);
v___x_2762_ = ((size_t)0ULL);
v___x_2763_ = lean_usize_of_nat(v___x_2752_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2750_, v___x_2762_, v___x_2763_, v___x_2753_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec_ref(v_alts_2750_);
return v___x_2764_;
}
}
else
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
lean_del_object(v___x_2748_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = lean_usize_of_nat(v___x_2752_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_alts_2750_, v___x_2765_, v___x_2766_, v___x_2753_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec_ref(v_alts_2750_);
return v___x_2767_;
}
}
}
}
case 5:
{
lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2776_; 
v_isSharedCheck_2776_ = !lean_is_exclusive(v_c_2721_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; 
v_unused_2777_ = lean_ctor_get(v_c_2721_, 0);
lean_dec(v_unused_2777_);
v___x_2770_ = v_c_2721_;
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_c_2721_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_box(0);
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2772_);
v___x_2774_ = v___x_2770_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
case 6:
{
lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2785_; 
v_isSharedCheck_2785_ = !lean_is_exclusive(v_c_2721_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_c_2721_, 0);
lean_dec(v_unused_2786_);
v___x_2779_ = v_c_2721_;
v_isShared_2780_ = v_isSharedCheck_2785_;
goto v_resetjp_2778_;
}
else
{
lean_dec(v_c_2721_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2785_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = lean_box(0);
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2781_);
v___x_2783_ = v___x_2779_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
case 8:
{
lean_object* v_k_2787_; 
v_k_2787_ = lean_ctor_get(v_c_2721_, 3);
lean_inc_ref(v_k_2787_);
lean_dec_ref_known(v_c_2721_, 4);
v_c_2721_ = v_k_2787_;
goto _start;
}
case 9:
{
lean_object* v_k_2789_; 
v_k_2789_ = lean_ctor_get(v_c_2721_, 5);
lean_inc_ref(v_k_2789_);
lean_dec_ref_known(v_c_2721_, 6);
v_c_2721_ = v_k_2789_;
goto _start;
}
default: 
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_dec_ref(v_c_2721_);
v___x_2791_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___closed__1);
v___x_2792_ = l_panic___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__1(v___x_2791_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
return v___x_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(lean_object* v_as_2793_, size_t v_i_2794_, size_t v_stop_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___y_2804_; uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_eq(v_i_2794_, v_stop_2795_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_array_uget_borrowed(v_as_2793_, v_i_2794_);
switch(lean_obj_tag(v___x_2811_))
{
case 0:
{
lean_object* v_code_2812_; 
v_code_2812_ = lean_ctor_get(v___x_2811_, 2);
lean_inc_ref(v_code_2812_);
v___y_2804_ = v_code_2812_;
goto v___jp_2803_;
}
case 1:
{
lean_object* v_code_2813_; 
v_code_2813_ = lean_ctor_get(v___x_2811_, 1);
lean_inc_ref(v_code_2813_);
v___y_2804_ = v_code_2813_;
goto v___jp_2803_;
}
default: 
{
lean_object* v_code_2814_; 
v_code_2814_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_ref(v_code_2814_);
v___y_2804_ = v_code_2814_;
goto v___jp_2803_;
}
}
}
else
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v_b_2796_);
return v___x_2815_;
}
v___jp_2803_:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v___y_2804_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; size_t v___x_2807_; size_t v___x_2808_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = ((size_t)1ULL);
v___x_2808_ = lean_usize_add(v_i_2794_, v___x_2807_);
v_i_2794_ = v___x_2808_;
v_b_2796_ = v_a_2806_;
goto _start;
}
else
{
return v___x_2805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0___boxed(lean_object* v_as_2816_, lean_object* v_i_2817_, lean_object* v_stop_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
size_t v_i_boxed_2826_; size_t v_stop_boxed_2827_; lean_object* v_res_2828_; 
v_i_boxed_2826_ = lean_unbox_usize(v_i_2817_);
lean_dec(v_i_2817_);
v_stop_boxed_2827_ = lean_unbox_usize(v_stop_2818_);
lean_dec(v_stop_2818_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets_spec__0(v_as_2816_, v_i_boxed_2826_, v_stop_boxed_2827_, v_b_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v_as_2816_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets___boxed(lean_object* v_c_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_c_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
return v_res_2836_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2837_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__0);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_object* v_00_u03b2_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0___closed__1);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(lean_object* v_f_2842_, lean_object* v_v_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
if (lean_obj_tag(v_v_2843_) == 0)
{
lean_object* v_code_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2874_; 
v_code_2850_ = lean_ctor_get(v_v_2843_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_v_2843_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2852_ = v_v_2843_;
v_isShared_2853_ = v_isSharedCheck_2874_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_code_2850_);
lean_dec(v_v_2843_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2874_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; 
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc_ref(v___y_2844_);
v___x_2854_ = lean_apply_7(v_f_2842_, v_code_2850_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, lean_box(0));
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2865_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2865_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2865_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v_a_2855_);
v___x_2860_ = v___x_2852_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2860_);
v___x_2862_ = v___x_2857_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_del_object(v___x_2852_);
v_a_2866_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2854_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2854_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
else
{
lean_object* v___x_2875_; 
lean_dec_ref(v_f_2842_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_v_2843_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg___boxed(lean_object* v_f_2876_, lean_object* v_v_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2876_, v_v_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v___y_2878_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(uint8_t v_pu_2885_, lean_object* v_f_2886_, lean_object* v_v_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v_f_2886_, v_v_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___boxed(lean_object* v_pu_2895_, lean_object* v_f_2896_, lean_object* v_v_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
uint8_t v_pu_boxed_2904_; lean_object* v_res_2905_; 
v_pu_boxed_2904_ = lean_unbox(v_pu_2895_);
v_res_2905_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1(v_pu_boxed_2904_, v_f_2896_, v_v_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2905_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__0(lean_box(0));
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(lean_object* v_code_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_alreadyFound_2915_; uint8_t v_relaxedReuse_2916_; lean_object* v_ownedness_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; uint8_t v_relaxedReuse_2924_; 
v_relaxedReuse_2924_ = lean_ctor_get_uint8(v___y_2908_, sizeof(void*)*2);
if (v_relaxedReuse_2924_ == 0)
{
lean_object* v_ownedness_2925_; lean_object* v___x_2926_; 
v_ownedness_2925_ = lean_ctor_get(v___y_2908_, 1);
v___x_2926_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v_alreadyFound_2915_ = v___x_2926_;
v_relaxedReuse_2916_ = v_relaxedReuse_2924_;
v_ownedness_2917_ = v_ownedness_2925_;
v___y_2918_ = v___y_2909_;
v___y_2919_ = v___y_2910_;
v___y_2920_ = v___y_2911_;
v___y_2921_ = v___y_2912_;
goto v___jp_2914_;
}
else
{
lean_object* v_ownedness_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_ownedness_2927_ = lean_ctor_get(v___y_2908_, 1);
v___x_2928_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_2929_ = lean_st_mk_ref(v___x_2928_);
lean_inc_ref(v_code_2907_);
v___x_2930_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_collectResets(v_code_2907_, v___x_2929_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v___x_2931_; 
lean_dec_ref_known(v___x_2930_, 1);
v___x_2931_ = lean_st_ref_get(v___x_2929_);
lean_dec(v___x_2929_);
v_alreadyFound_2915_ = v___x_2931_;
v_relaxedReuse_2916_ = v_relaxedReuse_2924_;
v_ownedness_2917_ = v_ownedness_2927_;
v___y_2918_ = v___y_2909_;
v___y_2919_ = v___y_2910_;
v___y_2920_ = v___y_2911_;
v___y_2921_ = v___y_2912_;
goto v___jp_2914_;
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v___x_2929_);
lean_dec_ref(v_code_2907_);
v_a_2932_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2930_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2930_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
v___jp_2914_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_inc_ref(v_ownedness_2917_);
v___x_2922_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2922_, 0, v_alreadyFound_2915_);
lean_ctor_set(v___x_2922_, 1, v_ownedness_2917_);
lean_ctor_set_uint8(v___x_2922_, sizeof(void*)*2, v_relaxedReuse_2916_);
v___x_2923_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Code_insertResetReuse(v_code_2907_, v___x_2922_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec_ref_known(v___x_2922_, 2);
return v___x_2923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___boxed(lean_object* v_code_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0(v_code_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(lean_object* v_decl_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_toSignature_2956_; lean_object* v_value_2957_; uint8_t v_recursive_2958_; lean_object* v_inlineAttr_x3f_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2984_; 
v_toSignature_2956_ = lean_ctor_get(v_decl_2949_, 0);
v_value_2957_ = lean_ctor_get(v_decl_2949_, 1);
v_recursive_2958_ = lean_ctor_get_uint8(v_decl_2949_, sizeof(void*)*3);
v_inlineAttr_x3f_2959_ = lean_ctor_get(v_decl_2949_, 2);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_decl_2949_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2961_ = v_decl_2949_;
v_isShared_2962_ = v_isSharedCheck_2984_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_inlineAttr_x3f_2959_);
lean_inc(v_value_2957_);
lean_inc(v_toSignature_2956_);
lean_dec(v_decl_2949_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2984_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___f_2963_; lean_object* v___x_2964_; 
v___f_2963_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___closed__0));
v___x_2964_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore_spec__1___redArg(v___f_2963_, v_value_2957_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2975_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v_a_2965_);
v___x_2970_ = v___x_2961_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_toSignature_2956_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_a_2965_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_inlineAttr_x3f_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, sizeof(void*)*3, v_recursive_2958_);
v___x_2970_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_del_object(v___x_2961_);
lean_dec(v_inlineAttr_x3f_2959_);
lean_dec_ref(v_toSignature_2956_);
v_a_2976_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2964_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2964_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___boxed(lean_object* v_decl_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_decl_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec_ref(v_a_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(lean_object* v_decl_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2994_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3027_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3027_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3027_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
uint8_t v_resetReuse_3004_; 
v_resetReuse_3004_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*4 + 2);
lean_dec(v_a_3000_);
if (v_resetReuse_3004_ == 0)
{
lean_object* v___x_3006_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v_decl_2993_);
v___x_3006_ = v___x_3002_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_decl_2993_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
else
{
lean_object* v___x_3008_; 
lean_del_object(v___x_3002_);
lean_inc_ref(v_decl_2993_);
v___x_3008_ = l_Lean_Compiler_LCNF_Decl_analyzePropagatedBorrows(v_decl_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc_n(v_a_3009_, 2);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Compiler_LCNF_Decl_applyOwnedness(v_decl_2993_, v_a_3009_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore___lam__0___closed__0);
v___x_3013_ = 0;
lean_inc(v_a_3009_);
v___x_3014_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v_a_3009_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*2, v___x_3013_);
v___x_3015_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3011_, v___x_3014_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec_ref_known(v___x_3014_, 2);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3017_, 0, v___x_3012_);
lean_ctor_set(v___x_3017_, 1, v_a_3009_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*2, v_resetReuse_3004_);
v___x_3018_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuseCore(v_a_3016_, v___x_3017_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec_ref_known(v___x_3017_, 2);
return v___x_3018_;
}
else
{
lean_dec(v_a_3009_);
return v___x_3015_;
}
}
else
{
lean_dec(v_a_3009_);
return v___x_3010_;
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v_decl_2993_);
v_a_3019_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3008_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3008_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v_decl_2993_);
v_a_3028_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2999_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2999_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse___boxed(lean_object* v_decl_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_Decl_insertResetReuse(v_decl_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
return v_res_3042_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__2));
v___x_3049_ = 2;
v___x_3050_ = ((lean_object*)(l_Lean_Compiler_LCNF_insertResetReuse___closed__1));
v___x_3051_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_3050_, v___x_3049_, v___x_3048_, v___x_3047_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_insertResetReuse(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_obj_once(&l_Lean_Compiler_LCNF_insertResetReuse___closed__3, &l_Lean_Compiler_LCNF_insertResetReuse___closed__3_once, _init_l_Lean_Compiler_LCNF_insertResetReuse___closed__3);
return v___x_3052_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = lean_unsigned_to_nat(2506150707u);
v___x_3109_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3110_ = l_Lean_Name_num___override(v___x_3109_, v___x_3108_);
return v___x_3110_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3113_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3114_ = l_Lean_Name_str___override(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3117_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3118_ = l_Lean_Name_str___override(v___x_3117_, v___x_3116_);
return v___x_3118_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_unsigned_to_nat(2u);
v___x_3120_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3121_ = l_Lean_Name_num___override(v___x_3120_, v___x_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_));
v___x_3124_ = 1;
v___x_3125_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_);
v___x_3126_ = l_Lean_registerTraceClass(v___x_3123_, v___x_3124_, v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2____boxed(lean_object* v_a_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l___private_Lean_Compiler_LCNF_ResetReuse_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ResetReuse_2506150707____hygCtx___hyg_2_();
return v_res_3128_;
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
