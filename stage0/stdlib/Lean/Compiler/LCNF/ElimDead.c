// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: public import Lean.Compiler.LCNF.PassManager
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elimDeadVars"};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadVars___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 0, 81, 239, 85, 207, 93, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_elimDeadVars___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_elimDeadVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 243, 129, 181, 154, 70, 99, 130)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ElimDead"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 82, 16, 255, 163, 142, 141, 196)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 8, 203, 14, 95, 80, 254, 83)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 234, 121, 60, 250, 43, 214, 104)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 227, 118, 194, 153, 141, 66, 82)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 178, 120, 48, 202, 193, 105)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 72, 106, 172, 157, 167, 211, 99)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(154, 254, 227, 186, 107, 229, 199, 236)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 208, 60, 24, 36, 96, 26, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 167, 57, 206, 2, 48, 8, 63)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 61, 197, 124, 13, 119, 183, 129)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 167, 154, 33, 100, 235, 233, 237)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(792928910) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(49, 145, 23, 34, 28, 29, 91, 149)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 85, 234, 87, 122, 159, 213, 105)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 221, 1, 151, 193, 161, 193, 61)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(79, 252, 64, 212, 189, 9, 17, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(lean_object* v_s_1_, lean_object* v_arg_2_){
_start:
{
if (lean_obj_tag(v_arg_2_) == 1)
{
lean_object* v_fvarId_3_; lean_object* v___x_4_; 
v_fvarId_3_ = lean_ctor_get(v_arg_2_, 0);
lean_inc(v_fvarId_3_);
lean_dec_ref_known(v_arg_2_, 1);
v___x_4_ = l_Lean_FVarIdSet_insert(v_s_1_, v_fvarId_3_);
return v___x_4_;
}
else
{
lean_dec(v_arg_2_);
return v_s_1_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(uint8_t v_pu_5_, lean_object* v_s_6_, lean_object* v_arg_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_s_6_, v_arg_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object* v_pu_9_, lean_object* v_s_10_, lean_object* v_arg_11_){
_start:
{
uint8_t v_pu_boxed_12_; lean_object* v_res_13_; 
v_pu_boxed_12_ = lean_unbox(v_pu_9_);
v_res_13_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg(v_pu_boxed_12_, v_s_10_, v_arg_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(lean_object* v_as_14_, size_t v_i_15_, size_t v_stop_16_, lean_object* v_b_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_eq(v_i_15_, v_stop_16_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; lean_object* v___x_20_; size_t v___x_21_; size_t v___x_22_; 
v___x_19_ = lean_array_uget_borrowed(v_as_14_, v_i_15_);
lean_inc(v___x_19_);
v___x_20_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v_b_17_, v___x_19_);
v___x_21_ = ((size_t)1ULL);
v___x_22_ = lean_usize_add(v_i_15_, v___x_21_);
v_i_15_ = v___x_22_;
v_b_17_ = v___x_20_;
goto _start;
}
else
{
return v_b_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg___boxed(lean_object* v_as_24_, lean_object* v_i_25_, lean_object* v_stop_26_, lean_object* v_b_27_){
_start:
{
size_t v_i_boxed_28_; size_t v_stop_boxed_29_; lean_object* v_res_30_; 
v_i_boxed_28_ = lean_unbox_usize(v_i_25_);
lean_dec(v_i_25_);
v_stop_boxed_29_ = lean_unbox_usize(v_stop_26_);
lean_dec(v_stop_26_);
v_res_30_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_24_, v_i_boxed_28_, v_stop_boxed_29_, v_b_27_);
lean_dec_ref(v_as_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(uint8_t v_pu_31_, lean_object* v_s_32_, lean_object* v_args_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_array_get_size(v_args_33_);
v___x_36_ = lean_nat_dec_lt(v___x_34_, v___x_35_);
if (v___x_36_ == 0)
{
return v_s_32_;
}
else
{
uint8_t v___x_37_; 
v___x_37_ = lean_nat_dec_le(v___x_35_, v___x_35_);
if (v___x_37_ == 0)
{
if (v___x_36_ == 0)
{
return v_s_32_;
}
else
{
size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; 
v___x_38_ = ((size_t)0ULL);
v___x_39_ = lean_usize_of_nat(v___x_35_);
v___x_40_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_33_, v___x_38_, v___x_39_, v_s_32_);
return v___x_40_;
}
}
else
{
size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = ((size_t)0ULL);
v___x_42_ = lean_usize_of_nat(v___x_35_);
v___x_43_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_33_, v___x_41_, v___x_42_, v_s_32_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* v_pu_44_, lean_object* v_s_45_, lean_object* v_args_46_){
_start:
{
uint8_t v_pu_boxed_47_; lean_object* v_res_48_; 
v_pu_boxed_47_ = lean_unbox(v_pu_44_);
v_res_48_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_boxed_47_, v_s_45_, v_args_46_);
lean_dec_ref(v_args_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t v_pu_49_, lean_object* v_as_50_, size_t v_i_51_, size_t v_stop_52_, lean_object* v_b_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_50_, v_i_51_, v_stop_52_, v_b_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* v_pu_55_, lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_stop_58_, lean_object* v_b_59_){
_start:
{
uint8_t v_pu_boxed_60_; size_t v_i_boxed_61_; size_t v_stop_boxed_62_; lean_object* v_res_63_; 
v_pu_boxed_60_ = lean_unbox(v_pu_55_);
v_i_boxed_61_ = lean_unbox_usize(v_i_57_);
lean_dec(v_i_57_);
v_stop_boxed_62_ = lean_unbox_usize(v_stop_58_);
lean_dec(v_stop_58_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_60_, v_as_56_, v_i_boxed_61_, v_stop_boxed_62_, v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t v_pu_64_, lean_object* v_s_65_, lean_object* v_e_66_){
_start:
{
switch(lean_obj_tag(v_e_66_))
{
case 2:
{
lean_object* v_struct_67_; lean_object* v___x_68_; 
v_struct_67_ = lean_ctor_get(v_e_66_, 2);
lean_inc(v_struct_67_);
lean_dec_ref_known(v_e_66_, 3);
v___x_68_ = l_Lean_FVarIdSet_insert(v_s_65_, v_struct_67_);
return v___x_68_;
}
case 3:
{
lean_object* v_args_69_; lean_object* v___x_70_; 
v_args_69_ = lean_ctor_get(v_e_66_, 2);
lean_inc_ref(v_args_69_);
lean_dec_ref_known(v_e_66_, 3);
v___x_70_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_69_);
lean_dec_ref(v_args_69_);
return v___x_70_;
}
case 4:
{
lean_object* v_fvarId_71_; lean_object* v_args_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_fvarId_71_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_fvarId_71_);
v_args_72_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_72_);
lean_dec_ref_known(v_e_66_, 2);
v___x_73_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_71_);
v___x_74_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v___x_73_, v_args_72_);
lean_dec_ref(v_args_72_);
return v___x_74_;
}
case 5:
{
lean_object* v_args_75_; lean_object* v___x_76_; 
v_args_75_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_75_);
lean_dec_ref_known(v_e_66_, 2);
v___x_76_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_75_);
lean_dec_ref(v_args_75_);
return v___x_76_;
}
case 6:
{
lean_object* v_var_77_; lean_object* v___x_78_; 
v_var_77_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_var_77_);
lean_dec_ref_known(v_e_66_, 2);
v___x_78_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_77_);
return v___x_78_;
}
case 7:
{
lean_object* v_var_79_; lean_object* v___x_80_; 
v_var_79_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_var_79_);
lean_dec_ref_known(v_e_66_, 2);
v___x_80_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_79_);
return v___x_80_;
}
case 8:
{
lean_object* v_var_81_; lean_object* v___x_82_; 
v_var_81_ = lean_ctor_get(v_e_66_, 2);
lean_inc(v_var_81_);
lean_dec_ref_known(v_e_66_, 3);
v___x_82_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_81_);
return v___x_82_;
}
case 9:
{
lean_object* v_args_83_; lean_object* v___x_84_; 
v_args_83_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_83_);
lean_dec_ref_known(v_e_66_, 2);
v___x_84_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_83_);
lean_dec_ref(v_args_83_);
return v___x_84_;
}
case 10:
{
lean_object* v_args_85_; lean_object* v___x_86_; 
v_args_85_ = lean_ctor_get(v_e_66_, 1);
lean_inc_ref(v_args_85_);
lean_dec_ref_known(v_e_66_, 2);
v___x_86_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v_s_65_, v_args_85_);
lean_dec_ref(v_args_85_);
return v___x_86_;
}
case 11:
{
lean_object* v_var_87_; lean_object* v___x_88_; 
v_var_87_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_var_87_);
lean_dec_ref_known(v_e_66_, 2);
v___x_88_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_87_);
return v___x_88_;
}
case 12:
{
lean_object* v_var_89_; lean_object* v_args_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_var_89_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_var_89_);
v_args_90_ = lean_ctor_get(v_e_66_, 2);
lean_inc_ref(v_args_90_);
lean_dec_ref_known(v_e_66_, 3);
v___x_91_ = l_Lean_FVarIdSet_insert(v_s_65_, v_var_89_);
v___x_92_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_64_, v___x_91_, v_args_90_);
lean_dec_ref(v_args_90_);
return v___x_92_;
}
case 13:
{
lean_object* v_fvarId_93_; lean_object* v___x_94_; 
v_fvarId_93_ = lean_ctor_get(v_e_66_, 1);
lean_inc(v_fvarId_93_);
lean_dec_ref_known(v_e_66_, 2);
v___x_94_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_93_);
return v___x_94_;
}
case 14:
{
lean_object* v_fvarId_95_; lean_object* v___x_96_; 
v_fvarId_95_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_fvarId_95_);
lean_dec_ref_known(v_e_66_, 1);
v___x_96_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_95_);
return v___x_96_;
}
case 15:
{
lean_object* v_fvarId_97_; lean_object* v___x_98_; 
v_fvarId_97_ = lean_ctor_get(v_e_66_, 0);
lean_inc(v_fvarId_97_);
lean_dec_ref_known(v_e_66_, 1);
v___x_98_ = l_Lean_FVarIdSet_insert(v_s_65_, v_fvarId_97_);
return v___x_98_;
}
default: 
{
lean_dec(v_e_66_);
return v_s_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object* v_pu_99_, lean_object* v_s_100_, lean_object* v_e_101_){
_start:
{
uint8_t v_pu_boxed_102_; lean_object* v_res_103_; 
v_pu_boxed_102_ = lean_unbox(v_pu_99_);
v_res_103_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_boxed_102_, v_s_100_, v_e_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object* v_arg_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_107_ = lean_st_ref_take(v_a_105_);
v___x_108_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_107_, v_arg_104_);
v___x_109_ = lean_st_ref_put(v_a_105_, v___x_108_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object* v_arg_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(v_arg_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t v_pu_116_, lean_object* v_arg_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_124_ = lean_st_ref_take(v_a_118_);
v___x_125_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_124_, v_arg_117_);
v___x_126_ = lean_st_ref_put(v_a_118_, v___x_125_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object* v_pu_129_, lean_object* v_arg_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_pu_boxed_137_; lean_object* v_res_138_; 
v_pu_boxed_137_ = lean_unbox(v_pu_129_);
v_res_138_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(v_pu_boxed_137_, v_arg_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t v_pu_139_, lean_object* v_e_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_143_ = lean_st_ref_take(v_a_141_);
v___x_144_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_139_, v___x_143_, v_e_140_);
v___x_145_ = lean_st_ref_put(v_a_141_, v___x_144_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object* v_pu_148_, lean_object* v_e_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
uint8_t v_pu_boxed_152_; lean_object* v_res_153_; 
v_pu_boxed_152_ = lean_unbox(v_pu_148_);
v_res_153_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(v_pu_boxed_152_, v_e_149_, v_a_150_);
lean_dec(v_a_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t v_pu_154_, lean_object* v_e_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_162_ = lean_st_ref_take(v_a_156_);
v___x_163_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_154_, v___x_162_, v_e_155_);
v___x_164_ = lean_st_ref_put(v_a_156_, v___x_163_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object* v_pu_167_, lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
uint8_t v_pu_boxed_175_; lean_object* v_res_176_; 
v_pu_boxed_175_ = lean_unbox(v_pu_167_);
v_res_176_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(v_pu_boxed_175_, v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object* v_fvarId_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = lean_st_ref_take(v_a_178_);
v___x_181_ = l_Lean_FVarIdSet_insert(v___x_180_, v_fvarId_177_);
v___x_182_ = lean_st_ref_put(v_a_178_, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object* v_fvarId_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(v_fvarId_185_, v_a_186_);
lean_dec(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object* v_fvarId_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = lean_st_ref_take(v_a_190_);
v___x_197_ = l_Lean_FVarIdSet_insert(v___x_196_, v_fvarId_189_);
v___x_198_ = lean_st_ref_put(v_a_190_, v___x_197_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object* v_fvarId_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(v_fvarId_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
return v_res_208_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t v_pu_209_, lean_object* v_val_210_){
_start:
{
if (v_pu_209_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
else
{
switch(lean_obj_tag(v_val_210_))
{
case 1:
{
uint8_t v___x_212_; 
v___x_212_ = 1;
return v___x_212_;
}
case 4:
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
case 9:
{
lean_object* v_args_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_args_214_ = lean_ctor_get(v_val_210_, 1);
v___x_215_ = lean_array_get_size(v_args_214_);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_nat_dec_eq(v___x_215_, v___x_216_);
return v___x_217_;
}
default: 
{
uint8_t v___x_218_; 
v___x_218_ = 1;
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object* v_pu_219_, lean_object* v_val_220_){
_start:
{
uint8_t v_pu_boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v_pu_boxed_221_ = lean_unbox(v_pu_219_);
v_res_222_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_boxed_221_, v_val_220_);
lean_dec(v_val_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object* v_as_224_, size_t v_i_225_, size_t v_stop_226_, lean_object* v_b_227_, lean_object* v___y_228_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_usize_dec_eq(v_i_225_, v_stop_226_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; size_t v___x_236_; size_t v___x_237_; 
v___x_231_ = lean_st_ref_take(v___y_228_);
v___x_232_ = lean_array_uget_borrowed(v_as_224_, v_i_225_);
lean_inc(v___x_232_);
v___x_233_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_231_, v___x_232_);
v___x_234_ = lean_st_ref_put(v___y_228_, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_add(v_i_225_, v___x_236_);
v_i_225_ = v___x_237_;
v_b_227_ = v___x_235_;
goto _start;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v_b_227_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object* v_as_240_, lean_object* v_i_241_, lean_object* v_stop_242_, lean_object* v_b_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
size_t v_i_boxed_246_; size_t v_stop_boxed_247_; lean_object* v_res_248_; 
v_i_boxed_246_ = lean_unbox_usize(v_i_241_);
lean_dec(v_i_241_);
v_stop_boxed_247_ = lean_unbox_usize(v_stop_242_);
lean_dec(v_stop_242_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_240_, v_i_boxed_246_, v_stop_boxed_247_, v_b_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v_as_240_);
return v_res_248_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object* v_k_249_, lean_object* v_t_250_){
_start:
{
if (lean_obj_tag(v_t_250_) == 0)
{
lean_object* v_k_251_; lean_object* v_l_252_; lean_object* v_r_253_; uint8_t v___x_254_; 
v_k_251_ = lean_ctor_get(v_t_250_, 1);
v_l_252_ = lean_ctor_get(v_t_250_, 3);
v_r_253_ = lean_ctor_get(v_t_250_, 4);
v___x_254_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_249_, v_k_251_);
switch(v___x_254_)
{
case 0:
{
v_t_250_ = v_l_252_;
goto _start;
}
case 1:
{
uint8_t v___x_256_; 
v___x_256_ = 1;
return v___x_256_;
}
default: 
{
v_t_250_ = v_r_253_;
goto _start;
}
}
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object* v_k_259_, lean_object* v_t_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_259_, v_t_260_);
lean_dec(v_t_260_);
lean_dec(v_k_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t v_pu_263_, lean_object* v_i_264_, lean_object* v_as_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_array_get_size(v_as_265_);
v___x_273_ = lean_nat_dec_lt(v_i_264_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec(v_i_264_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v_as_265_);
return v___x_274_;
}
else
{
lean_object* v_a_275_; lean_object* v___y_277_; 
v_a_275_ = lean_array_fget_borrowed(v_as_265_, v_i_264_);
switch(lean_obj_tag(v_a_275_))
{
case 0:
{
lean_object* v_code_299_; 
v_code_299_ = lean_ctor_get(v_a_275_, 2);
lean_inc_ref(v_code_299_);
v___y_277_ = v_code_299_;
goto v___jp_276_;
}
case 1:
{
lean_object* v_code_300_; 
v_code_300_ = lean_ctor_get(v_a_275_, 1);
lean_inc_ref(v_code_300_);
v___y_277_ = v_code_300_;
goto v___jp_276_;
}
default: 
{
lean_object* v_code_301_; 
v_code_301_ = lean_ctor_get(v_a_275_, 0);
lean_inc_ref(v_code_301_);
v___y_277_ = v_code_301_;
goto v___jp_276_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; 
v___x_278_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_263_, v___y_277_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; size_t v___x_281_; size_t v___x_282_; uint8_t v___x_283_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
lean_inc(v_a_275_);
v___x_280_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_275_, v_a_279_);
v___x_281_ = lean_ptr_addr(v_a_275_);
v___x_282_ = lean_ptr_addr(v___x_280_);
v___x_283_ = lean_usize_dec_eq(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_264_, v___x_284_);
v___x_286_ = lean_array_fset(v_as_265_, v_i_264_, v___x_280_);
lean_dec(v_i_264_);
v_i_264_ = v___x_285_;
v_as_265_ = v___x_286_;
goto _start;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref(v___x_280_);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_i_264_, v___x_288_);
lean_dec(v_i_264_);
v_i_264_ = v___x_289_;
goto _start;
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_as_265_);
lean_dec(v_i_264_);
v_a_291_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_278_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_278_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t v_pu_302_, lean_object* v_code_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___y_311_; 
switch(lean_obj_tag(v_code_303_))
{
case 0:
{
lean_object* v_decl_328_; lean_object* v_k_329_; lean_object* v___x_330_; 
v_decl_328_ = lean_ctor_get(v_code_303_, 0);
v_k_329_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_329_);
v___x_330_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_329_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_381_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_381_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_381_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_381_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_fvarId_336_; lean_object* v_value_337_; uint8_t v___y_361_; uint8_t v___x_379_; 
v___x_335_ = lean_st_ref_get(v_a_304_);
v_fvarId_336_ = lean_ctor_get(v_decl_328_, 0);
v_value_337_ = lean_ctor_get(v_decl_328_, 3);
v___x_379_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_336_, v___x_335_);
lean_dec(v___x_335_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_302_, v_value_337_);
if (v___x_380_ == 0)
{
goto v___jp_338_;
}
else
{
v___y_361_ = v___x_379_;
goto v___jp_360_;
}
}
else
{
v___y_361_ = v___x_379_;
goto v___jp_360_;
}
v___jp_338_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; uint8_t v___x_344_; 
v___x_339_ = lean_st_ref_take(v_a_304_);
lean_inc(v_value_337_);
v___x_340_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_302_, v___x_339_, v_value_337_);
v___x_341_ = lean_st_ref_put(v_a_304_, v___x_340_);
v___x_342_ = lean_ptr_addr(v_k_329_);
v___x_343_ = lean_ptr_addr(v_a_331_);
v___x_344_ = lean_usize_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_354_; 
lean_inc_ref(v_decl_328_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_355_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_356_);
v___x_346_ = v_code_303_;
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_code_303_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_a_331_);
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_decl_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_a_331_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_349_);
v___x_351_ = v___x_333_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v_code_303_);
v___x_358_ = v___x_333_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_code_303_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
v___jp_360_:
{
if (v___y_361_ == 0)
{
lean_object* v___x_362_; 
lean_inc_ref(v_decl_328_);
lean_del_object(v___x_333_);
lean_dec_ref_known(v_code_303_, 2);
v___x_362_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_302_, v_decl_328_, v_a_306_);
lean_dec_ref(v_decl_328_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_370_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_a_331_);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_331_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_331_);
v_a_371_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_362_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
goto v___jp_338_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_330_;
}
}
case 1:
{
lean_object* v_decl_382_; lean_object* v_k_383_; lean_object* v___x_384_; 
v_decl_382_ = lean_ctor_get(v_code_303_, 0);
v_k_383_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_383_);
v___x_384_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_383_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v_fvarId_387_; uint8_t v___x_388_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = lean_st_ref_get(v_a_304_);
v_fvarId_387_ = lean_ctor_get(v_decl_382_, 0);
v___x_388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_387_, v___x_386_);
lean_dec(v___x_386_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; lean_object* v___x_390_; 
lean_inc_ref(v_decl_382_);
lean_dec_ref_known(v_code_303_, 2);
v___x_389_ = 1;
v___x_390_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_302_, v_decl_382_, v___x_389_, v_a_306_);
lean_dec_ref(v_decl_382_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_398_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v_a_385_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_385_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_385_);
v_a_399_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_390_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_390_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_407_; 
lean_inc_ref(v_decl_382_);
v___x_407_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_302_, v_decl_382_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_445_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_445_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_445_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_445_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
size_t v___x_412_; size_t v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_ptr_addr(v_k_383_);
v___x_413_ = lean_ptr_addr(v_a_385_);
v___x_414_ = lean_usize_dec_eq(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_424_; 
v_isSharedCheck_424_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_426_);
v___x_416_ = v_code_303_;
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_code_303_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v_a_385_);
lean_ctor_set(v___x_416_, 0, v_a_408_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_a_385_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_419_);
v___x_421_ = v___x_410_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
size_t v___x_427_; size_t v___x_428_; uint8_t v___x_429_; 
v___x_427_ = lean_ptr_addr(v_decl_382_);
v___x_428_ = lean_ptr_addr(v_a_408_);
v___x_429_ = lean_usize_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_439_; 
v_isSharedCheck_439_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; lean_object* v_unused_441_; 
v_unused_440_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_441_);
v___x_431_ = v_code_303_;
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
else
{
lean_dec(v_code_303_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v_a_385_);
lean_ctor_set(v___x_431_, 0, v_a_408_);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_408_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_a_385_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_434_);
v___x_436_ = v___x_410_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
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
else
{
lean_object* v___x_443_; 
lean_dec(v_a_408_);
lean_dec(v_a_385_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_code_303_);
v___x_443_ = v___x_410_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_code_303_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_a_385_);
lean_dec_ref_known(v_code_303_, 2);
v_a_446_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_407_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_407_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_384_;
}
}
case 2:
{
lean_object* v_decl_454_; lean_object* v_k_455_; lean_object* v___x_456_; 
v_decl_454_ = lean_ctor_get(v_code_303_, 0);
v_k_455_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_455_);
v___x_456_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_455_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; lean_object* v_fvarId_459_; uint8_t v___x_460_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = lean_st_ref_get(v_a_304_);
v_fvarId_459_ = lean_ctor_get(v_decl_454_, 0);
v___x_460_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_459_, v___x_458_);
lean_dec(v___x_458_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; lean_object* v___x_462_; 
lean_inc_ref(v_decl_454_);
lean_dec_ref_known(v_code_303_, 2);
v___x_461_ = 1;
v___x_462_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_302_, v_decl_454_, v___x_461_, v_a_306_);
lean_dec_ref(v_decl_454_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v___x_462_, 0);
lean_dec(v_unused_470_);
v___x_464_ = v___x_462_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_462_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v_a_457_);
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_457_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v_a_457_);
v_a_471_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_462_);
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
lean_object* v___x_479_; 
lean_inc_ref(v_decl_454_);
v___x_479_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_302_, v_decl_454_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_517_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_517_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_517_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_517_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v___x_484_ = lean_ptr_addr(v_k_455_);
v___x_485_ = lean_ptr_addr(v_a_457_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_496_; 
v_isSharedCheck_496_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_497_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_498_);
v___x_488_ = v_code_303_;
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_code_303_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_496_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v_a_457_);
lean_ctor_set(v___x_488_, 0, v_a_480_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_457_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_491_);
v___x_493_ = v___x_482_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_ptr_addr(v_decl_454_);
v___x_500_ = lean_ptr_addr(v_a_480_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_511_; 
v_isSharedCheck_511_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; lean_object* v_unused_513_; 
v_unused_512_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_513_);
v___x_503_ = v_code_303_;
v_isShared_504_ = v_isSharedCheck_511_;
goto v_resetjp_502_;
}
else
{
lean_dec(v_code_303_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_511_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_a_457_);
lean_ctor_set(v___x_503_, 0, v_a_480_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_480_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_a_457_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_506_);
v___x_508_ = v___x_482_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
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
else
{
lean_object* v___x_515_; 
lean_dec(v_a_480_);
lean_dec(v_a_457_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_code_303_);
v___x_515_ = v___x_482_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_code_303_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_457_);
lean_dec_ref_known(v_code_303_, 2);
v_a_518_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_479_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_479_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_456_;
}
}
case 3:
{
lean_object* v_fvarId_526_; lean_object* v_args_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_fvarId_526_ = lean_ctor_get(v_code_303_, 0);
v_args_527_ = lean_ctor_get(v_code_303_, 1);
v___x_528_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_526_);
v___x_529_ = l_Lean_FVarIdSet_insert(v___x_528_, v_fvarId_526_);
v___x_530_ = lean_st_ref_put(v_a_304_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_args_527_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v_code_303_);
return v___x_534_;
}
else
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_nat_dec_le(v___x_532_, v___x_532_);
if (v___x_536_ == 0)
{
if (v___x_533_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_code_303_);
return v___x_537_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_532_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_527_, v___x_538_, v___x_539_, v___x_535_, v_a_304_);
v___y_311_ = v___x_540_;
goto v___jp_310_;
}
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((size_t)0ULL);
v___x_542_ = lean_usize_of_nat(v___x_532_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_527_, v___x_541_, v___x_542_, v___x_535_, v_a_304_);
v___y_311_ = v___x_543_;
goto v___jp_310_;
}
}
}
case 4:
{
lean_object* v_cases_544_; lean_object* v_typeName_545_; lean_object* v_resultType_546_; lean_object* v_discr_547_; lean_object* v_alts_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_590_; 
v_cases_544_ = lean_ctor_get(v_code_303_, 0);
lean_inc_ref(v_cases_544_);
v_typeName_545_ = lean_ctor_get(v_cases_544_, 0);
v_resultType_546_ = lean_ctor_get(v_cases_544_, 1);
v_discr_547_ = lean_ctor_get(v_cases_544_, 2);
v_alts_548_ = lean_ctor_get(v_cases_544_, 3);
v_isSharedCheck_590_ = !lean_is_exclusive(v_cases_544_);
if (v_isSharedCheck_590_ == 0)
{
v___x_550_ = v_cases_544_;
v_isShared_551_ = v_isSharedCheck_590_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_alts_548_);
lean_inc(v_discr_547_);
lean_inc(v_resultType_546_);
lean_inc(v_typeName_545_);
lean_dec(v_cases_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_590_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_548_);
v___x_553_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_302_, v___x_552_, v_alts_548_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_581_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_581_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_581_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_581_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; size_t v___x_561_; size_t v___x_562_; uint8_t v___x_563_; 
v___x_558_ = lean_st_ref_take(v_a_304_);
lean_inc(v_discr_547_);
v___x_559_ = l_Lean_FVarIdSet_insert(v___x_558_, v_discr_547_);
v___x_560_ = lean_st_ref_put(v_a_304_, v___x_559_);
v___x_561_ = lean_ptr_addr(v_alts_548_);
lean_dec_ref(v_alts_548_);
v___x_562_ = lean_ptr_addr(v_a_554_);
v___x_563_ = lean_usize_dec_eq(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_576_; 
v_isSharedCheck_576_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_577_);
v___x_565_ = v_code_303_;
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
else
{
lean_dec(v_code_303_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 3, v_a_554_);
v___x_568_ = v___x_550_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_typeName_545_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_resultType_546_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_discr_547_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_a_554_);
v___x_568_ = v_reuseFailAlloc_575_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_572_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_570_);
v___x_572_ = v___x_556_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v_a_554_);
lean_del_object(v___x_550_);
lean_dec(v_discr_547_);
lean_dec_ref(v_resultType_546_);
lean_dec(v_typeName_545_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_code_303_);
v___x_579_ = v___x_556_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_code_303_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_del_object(v___x_550_);
lean_dec_ref(v_alts_548_);
lean_dec(v_discr_547_);
lean_dec_ref(v_resultType_546_);
lean_dec(v_typeName_545_);
lean_dec_ref_known(v_code_303_, 1);
v_a_582_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_553_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_553_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_fvarId_591_ = lean_ctor_get(v_code_303_, 0);
v___x_592_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_591_);
v___x_593_ = l_Lean_FVarIdSet_insert(v___x_592_, v_fvarId_591_);
v___x_594_ = lean_st_ref_put(v_a_304_, v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v_code_303_);
return v___x_595_;
}
case 6:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_code_303_);
return v___x_596_;
}
case 7:
{
lean_object* v_fvarId_597_; lean_object* v_i_598_; lean_object* v_y_599_; lean_object* v_k_600_; lean_object* v___x_601_; 
v_fvarId_597_ = lean_ctor_get(v_code_303_, 0);
v_i_598_ = lean_ctor_get(v_code_303_, 1);
v_y_599_ = lean_ctor_get(v_code_303_, 2);
v_k_600_ = lean_ctor_get(v_code_303_, 3);
lean_inc_ref(v_k_600_);
v___x_601_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_600_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_634_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_634_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_634_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_634_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_st_ref_get(v_a_304_);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_597_, v___x_606_);
lean_dec(v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref_known(v_code_303_, 4);
if (v_isShared_605_ == 0)
{
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_602_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; size_t v___x_614_; size_t v___x_615_; uint8_t v___x_616_; 
v___x_611_ = lean_st_ref_take(v_a_304_);
lean_inc(v_y_599_);
v___x_612_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_611_, v_y_599_);
v___x_613_ = lean_st_ref_put(v_a_304_, v___x_612_);
v___x_614_ = lean_ptr_addr(v_k_600_);
v___x_615_ = lean_ptr_addr(v_a_602_);
v___x_616_ = lean_usize_dec_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
lean_inc(v_y_599_);
lean_inc(v_i_598_);
lean_inc(v_fvarId_597_);
v_isSharedCheck_626_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_627_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_630_);
v___x_618_ = v_code_303_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_dec(v_code_303_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 3, v_a_602_);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_fvarId_597_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_i_598_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_y_599_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_a_602_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_621_);
v___x_623_ = v___x_604_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
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
else
{
lean_object* v___x_632_; 
lean_dec(v_a_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_code_303_);
v___x_632_ = v___x_604_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_code_303_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 4);
return v___x_601_;
}
}
case 8:
{
lean_object* v_fvarId_635_; lean_object* v_i_636_; lean_object* v_y_637_; lean_object* v_k_638_; lean_object* v___x_639_; 
v_fvarId_635_ = lean_ctor_get(v_code_303_, 0);
v_i_636_ = lean_ctor_get(v_code_303_, 1);
v_y_637_ = lean_ctor_get(v_code_303_, 2);
v_k_638_ = lean_ctor_get(v_code_303_, 3);
lean_inc_ref(v_k_638_);
v___x_639_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_638_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_672_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_672_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_672_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_672_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_st_ref_get(v_a_304_);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_635_, v___x_644_);
lean_dec(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; 
lean_dec_ref_known(v_code_303_, 4);
if (v_isShared_643_ == 0)
{
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_640_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
v___x_649_ = lean_st_ref_take(v_a_304_);
lean_inc(v_y_637_);
v___x_650_ = l_Lean_FVarIdSet_insert(v___x_649_, v_y_637_);
v___x_651_ = lean_st_ref_put(v_a_304_, v___x_650_);
v___x_652_ = lean_ptr_addr(v_k_638_);
v___x_653_ = lean_ptr_addr(v_a_640_);
v___x_654_ = lean_usize_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_664_; 
lean_inc(v_y_637_);
lean_inc(v_i_636_);
lean_inc(v_fvarId_635_);
v_isSharedCheck_664_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; lean_object* v_unused_666_; lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_665_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_668_);
v___x_656_ = v_code_303_;
v_isShared_657_ = v_isSharedCheck_664_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_code_303_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_664_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 3, v_a_640_);
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fvarId_635_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_i_636_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_y_637_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_a_640_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_659_);
v___x_661_ = v___x_642_;
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
}
}
else
{
lean_object* v___x_670_; 
lean_dec(v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_code_303_);
v___x_670_ = v___x_642_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_code_303_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 4);
return v___x_639_;
}
}
case 9:
{
lean_object* v_fvarId_673_; lean_object* v_i_674_; lean_object* v_offset_675_; lean_object* v_y_676_; lean_object* v_ty_677_; lean_object* v_k_678_; lean_object* v___x_679_; 
v_fvarId_673_ = lean_ctor_get(v_code_303_, 0);
v_i_674_ = lean_ctor_get(v_code_303_, 1);
v_offset_675_ = lean_ctor_get(v_code_303_, 2);
v_y_676_ = lean_ctor_get(v_code_303_, 3);
v_ty_677_ = lean_ctor_get(v_code_303_, 4);
v_k_678_ = lean_ctor_get(v_code_303_, 5);
lean_inc_ref(v_k_678_);
v___x_679_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_678_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_714_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_714_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_714_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_714_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_st_ref_get(v_a_304_);
v___x_685_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_673_, v___x_684_);
lean_dec(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref_known(v_code_303_, 6);
if (v_isShared_683_ == 0)
{
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_680_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; size_t v___x_692_; size_t v___x_693_; uint8_t v___x_694_; 
v___x_689_ = lean_st_ref_take(v_a_304_);
lean_inc(v_y_676_);
v___x_690_ = l_Lean_FVarIdSet_insert(v___x_689_, v_y_676_);
v___x_691_ = lean_st_ref_put(v_a_304_, v___x_690_);
v___x_692_ = lean_ptr_addr(v_k_678_);
v___x_693_ = lean_ptr_addr(v_a_680_);
v___x_694_ = lean_usize_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_704_; 
lean_inc_ref(v_ty_677_);
lean_inc(v_y_676_);
lean_inc(v_offset_675_);
lean_inc(v_i_674_);
lean_inc(v_fvarId_673_);
v_isSharedCheck_704_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_705_ = lean_ctor_get(v_code_303_, 5);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_code_303_, 4);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_710_);
v___x_696_ = v_code_303_;
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
else
{
lean_dec(v_code_303_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 5, v_a_680_);
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_fvarId_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_i_674_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_offset_675_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_y_676_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_ty_677_);
lean_ctor_set(v_reuseFailAlloc_703_, 5, v_a_680_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_699_);
v___x_701_ = v___x_682_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v___x_712_; 
lean_dec(v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_code_303_);
v___x_712_ = v___x_682_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_code_303_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 6);
return v___x_679_;
}
}
case 10:
{
lean_object* v_fvarId_715_; lean_object* v_cidx_716_; lean_object* v_k_717_; lean_object* v___x_718_; 
v_fvarId_715_ = lean_ctor_get(v_code_303_, 0);
v_cidx_716_ = lean_ctor_get(v_code_303_, 1);
v_k_717_ = lean_ctor_get(v_code_303_, 2);
lean_inc_ref(v_k_717_);
v___x_718_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_717_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_745_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_745_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_745_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_745_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; uint8_t v___x_728_; 
v___x_723_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_715_);
v___x_724_ = l_Lean_FVarIdSet_insert(v___x_723_, v_fvarId_715_);
v___x_725_ = lean_st_ref_put(v_a_304_, v___x_724_);
v___x_726_ = lean_ptr_addr(v_k_717_);
v___x_727_ = lean_ptr_addr(v_a_719_);
v___x_728_ = lean_usize_dec_eq(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_738_; 
lean_inc(v_cidx_716_);
lean_inc(v_fvarId_715_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; 
v_unused_739_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_741_);
v___x_730_ = v_code_303_;
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_code_303_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_738_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 2, v_a_719_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fvarId_715_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_cidx_716_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_a_719_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_733_);
v___x_735_ = v___x_721_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v_a_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_code_303_);
v___x_743_ = v___x_721_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_code_303_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 3);
return v___x_718_;
}
}
case 11:
{
lean_object* v_fvarId_746_; lean_object* v_n_747_; uint8_t v_check_748_; uint8_t v_persistent_749_; lean_object* v_k_750_; lean_object* v___x_751_; 
v_fvarId_746_ = lean_ctor_get(v_code_303_, 0);
v_n_747_ = lean_ctor_get(v_code_303_, 1);
v_check_748_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*3);
v_persistent_749_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*3 + 1);
v_k_750_ = lean_ctor_get(v_code_303_, 2);
lean_inc_ref(v_k_750_);
v___x_751_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_750_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_778_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_778_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_778_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_778_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; size_t v___x_759_; size_t v___x_760_; uint8_t v___x_761_; 
v___x_756_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_746_);
v___x_757_ = l_Lean_FVarIdSet_insert(v___x_756_, v_fvarId_746_);
v___x_758_ = lean_st_ref_put(v_a_304_, v___x_757_);
v___x_759_ = lean_ptr_addr(v_k_750_);
v___x_760_ = lean_ptr_addr(v_a_752_);
v___x_761_ = lean_usize_dec_eq(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_771_; 
lean_inc(v_n_747_);
lean_inc(v_fvarId_746_);
v_isSharedCheck_771_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; 
v_unused_772_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_774_);
v___x_763_ = v_code_303_;
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_code_303_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v_a_752_);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_fvarId_746_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_n_747_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_a_752_);
lean_ctor_set_uint8(v_reuseFailAlloc_770_, sizeof(void*)*3, v_check_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_770_, sizeof(void*)*3 + 1, v_persistent_749_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_766_);
v___x_768_ = v___x_754_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec(v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_code_303_);
v___x_776_ = v___x_754_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_code_303_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 3);
return v___x_751_;
}
}
case 12:
{
lean_object* v_fvarId_779_; lean_object* v_n_780_; uint8_t v_check_781_; uint8_t v_persistent_782_; lean_object* v_objs_x3f_783_; lean_object* v_k_784_; lean_object* v___x_785_; 
v_fvarId_779_ = lean_ctor_get(v_code_303_, 0);
v_n_780_ = lean_ctor_get(v_code_303_, 1);
v_check_781_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*4);
v_persistent_782_ = lean_ctor_get_uint8(v_code_303_, sizeof(void*)*4 + 1);
v_objs_x3f_783_ = lean_ctor_get(v_code_303_, 2);
v_k_784_ = lean_ctor_get(v_code_303_, 3);
lean_inc_ref(v_k_784_);
v___x_785_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_784_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_813_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_813_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_813_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_813_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; uint8_t v___x_795_; 
v___x_790_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_779_);
v___x_791_ = l_Lean_FVarIdSet_insert(v___x_790_, v_fvarId_779_);
v___x_792_ = lean_st_ref_put(v_a_304_, v___x_791_);
v___x_793_ = lean_ptr_addr(v_k_784_);
v___x_794_ = lean_ptr_addr(v_a_786_);
v___x_795_ = lean_usize_dec_eq(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_805_; 
lean_inc(v_objs_x3f_783_);
lean_inc(v_n_780_);
lean_inc(v_fvarId_779_);
v_isSharedCheck_805_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; 
v_unused_806_ = lean_ctor_get(v_code_303_, 3);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_code_303_, 2);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_809_);
v___x_797_ = v_code_303_;
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_code_303_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 3, v_a_786_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_fvarId_779_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_n_780_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_objs_x3f_783_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_a_786_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*4, v_check_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*4 + 1, v_persistent_782_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_800_);
v___x_802_ = v___x_788_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
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
else
{
lean_object* v___x_811_; 
lean_dec(v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_code_303_);
v___x_811_ = v___x_788_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_code_303_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 4);
return v___x_785_;
}
}
default: 
{
lean_object* v_fvarId_814_; lean_object* v_k_815_; lean_object* v___x_816_; 
v_fvarId_814_ = lean_ctor_get(v_code_303_, 0);
v_k_815_ = lean_ctor_get(v_code_303_, 1);
lean_inc_ref(v_k_815_);
v___x_816_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_302_, v_k_815_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_842_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_842_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_842_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_842_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; size_t v___x_824_; size_t v___x_825_; uint8_t v___x_826_; 
v___x_821_ = lean_st_ref_take(v_a_304_);
lean_inc(v_fvarId_814_);
v___x_822_ = l_Lean_FVarIdSet_insert(v___x_821_, v_fvarId_814_);
v___x_823_ = lean_st_ref_put(v_a_304_, v___x_822_);
v___x_824_ = lean_ptr_addr(v_k_815_);
v___x_825_ = lean_ptr_addr(v_a_817_);
v___x_826_ = lean_usize_dec_eq(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_fvarId_814_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_code_303_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_837_ = lean_ctor_get(v_code_303_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_code_303_, 0);
lean_dec(v_unused_838_);
v___x_828_ = v_code_303_;
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_code_303_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_836_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_a_817_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_fvarId_814_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_a_817_);
v___x_831_ = v_reuseFailAlloc_835_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_831_);
v___x_833_ = v___x_819_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec(v_a_817_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v_code_303_);
v___x_840_ = v___x_819_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_code_303_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_303_, 2);
return v___x_816_;
}
}
}
v___jp_310_:
{
if (lean_obj_tag(v___y_311_) == 0)
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_isSharedCheck_318_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v___y_311_, 0);
lean_dec(v_unused_319_);
v___x_313_ = v___y_311_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_dec(v___y_311_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v_code_303_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_code_303_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_code_303_);
v_a_320_ = lean_ctor_get(v___y_311_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___y_311_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___y_311_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t v_pu_843_, lean_object* v_funDecl_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_params_851_; lean_object* v_type_852_; lean_object* v_value_853_; lean_object* v___x_854_; 
v_params_851_ = lean_ctor_get(v_funDecl_844_, 2);
lean_inc_ref(v_params_851_);
v_type_852_ = lean_ctor_get(v_funDecl_844_, 3);
lean_inc_ref(v_type_852_);
v_value_853_ = lean_ctor_get(v_funDecl_844_, 4);
lean_inc_ref(v_value_853_);
v___x_854_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_843_, v_value_853_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_843_, v_funDecl_844_, v_type_852_, v_params_851_, v_a_855_, v_a_847_);
return v___x_856_;
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_type_852_);
lean_dec_ref(v_params_851_);
lean_dec_ref(v_funDecl_844_);
v_a_857_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_854_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_854_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object* v_pu_865_, lean_object* v_funDecl_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
uint8_t v_pu_boxed_873_; lean_object* v_res_874_; 
v_pu_boxed_873_ = lean_unbox(v_pu_865_);
v_res_874_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_boxed_873_, v_funDecl_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object* v_pu_875_, lean_object* v_i_876_, lean_object* v_as_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_pu_boxed_884_; lean_object* v_res_885_; 
v_pu_boxed_884_ = lean_unbox(v_pu_875_);
v_res_885_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_884_, v_i_876_, v_as_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* v_pu_886_, lean_object* v_code_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v_pu_boxed_894_; lean_object* v_res_895_; 
v_pu_boxed_894_ = lean_unbox(v_pu_886_);
v_res_895_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_boxed_894_, v_code_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
return v_res_895_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object* v_00_u03b2_896_, lean_object* v_k_897_, lean_object* v_t_898_){
_start:
{
uint8_t v___x_899_; 
v___x_899_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_897_, v_t_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object* v_00_u03b2_900_, lean_object* v_k_901_, lean_object* v_t_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_900_, v_k_901_, v_t_902_);
lean_dec(v_t_902_);
lean_dec(v_k_901_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t v_pu_905_, lean_object* v_as_906_, size_t v_i_907_, size_t v_stop_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_906_, v_i_907_, v_stop_908_, v_b_909_, v___y_910_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object* v_pu_917_, lean_object* v_as_918_, lean_object* v_i_919_, lean_object* v_stop_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_pu_boxed_928_; size_t v_i_boxed_929_; size_t v_stop_boxed_930_; lean_object* v_res_931_; 
v_pu_boxed_928_ = lean_unbox(v_pu_917_);
v_i_boxed_929_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_stop_boxed_930_ = lean_unbox_usize(v_stop_920_);
lean_dec(v_stop_920_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_928_, v_as_918_, v_i_boxed_929_, v_stop_boxed_930_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v_as_918_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object* v_f_932_, lean_object* v_v_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
if (lean_obj_tag(v_v_933_) == 0)
{
lean_object* v_code_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_963_; 
v_code_939_ = lean_ctor_get(v_v_933_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_v_933_);
if (v_isSharedCheck_963_ == 0)
{
v___x_941_ = v_v_933_;
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_code_939_);
lean_dec(v_v_933_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; 
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
v___x_943_ = lean_apply_6(v_f_932_, v_code_939_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, lean_box(0));
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_954_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_954_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_954_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_a_944_);
v___x_949_ = v___x_941_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_941_);
v_a_955_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_943_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_943_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v_f_932_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_v_933_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object* v_f_965_, lean_object* v_v_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_965_, v_v_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t v_pu_973_, lean_object* v_f_974_, lean_object* v_v_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_974_, v_v_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object* v_pu_982_, lean_object* v_f_983_, lean_object* v_v_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v_pu_boxed_990_; lean_object* v_res_991_; 
v_pu_boxed_990_ = lean_unbox(v_pu_982_);
v_res_991_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_990_, v_f_983_, v_v_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object* v___x_992_, uint8_t v_pu_993_, lean_object* v_code_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_st_mk_ref(v___x_992_);
v___x_1001_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_993_, v_code_994_, v___x_1000_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = lean_st_ref_get(v___x_1000_);
lean_dec(v___x_1000_);
lean_dec(v___x_1006_);
if (v_isShared_1005_ == 0)
{
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1002_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_dec(v___x_1000_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object* v___x_1011_, lean_object* v_pu_1012_, lean_object* v_code_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v_pu_boxed_1019_; lean_object* v_res_1020_; 
v_pu_boxed_1019_ = lean_unbox(v_pu_1012_);
v_res_1020_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(v___x_1011_, v_pu_boxed_1019_, v_code_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t v_pu_1021_, lean_object* v_decl_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_toSignature_1028_; lean_object* v_value_1029_; uint8_t v_recursive_1030_; lean_object* v_inlineAttr_x3f_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1058_; 
v_toSignature_1028_ = lean_ctor_get(v_decl_1022_, 0);
v_value_1029_ = lean_ctor_get(v_decl_1022_, 1);
v_recursive_1030_ = lean_ctor_get_uint8(v_decl_1022_, sizeof(void*)*3);
v_inlineAttr_x3f_1031_ = lean_ctor_get(v_decl_1022_, 2);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_decl_1022_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1033_ = v_decl_1022_;
v_isShared_1034_ = v_isSharedCheck_1058_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_inlineAttr_x3f_1031_);
lean_inc(v_value_1029_);
lean_inc(v_toSignature_1028_);
lean_dec(v_decl_1022_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1058_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; 
v___x_1035_ = lean_box(1);
v___x_1036_ = lean_box(v_pu_1021_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1037_, 0, v___x_1035_);
lean_closure_set(v___f_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_1037_, v_value_1029_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1049_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1049_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v_a_1039_);
v___x_1044_ = v___x_1033_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_toSignature_1028_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_a_1039_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_inlineAttr_x3f_1031_);
lean_ctor_set_uint8(v_reuseFailAlloc_1048_, sizeof(void*)*3, v_recursive_1030_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1044_);
v___x_1046_ = v___x_1041_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_del_object(v___x_1033_);
lean_dec(v_inlineAttr_x3f_1031_);
lean_dec_ref(v_toSignature_1028_);
v_a_1050_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1038_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1038_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object* v_pu_1059_, lean_object* v_decl_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_pu_boxed_1066_; lean_object* v_res_1067_; 
v_pu_boxed_1066_ = lean_unbox(v_pu_1059_);
v_res_1067_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v_pu_boxed_1066_, v_decl_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t v_phase_1071_, lean_object* v_occurrence_1072_){
_start:
{
lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1073_ = ((lean_object*)(l_Lean_Compiler_LCNF_elimDeadVars___closed__1));
v___x_1074_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1071_);
v___x_1075_ = lean_box(v___x_1074_);
v___x_1076_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed), 7, 1);
lean_closure_set(v___x_1076_, 0, v___x_1075_);
v___x_1077_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1073_, v_phase_1071_, v___x_1076_, v_occurrence_1072_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object* v_phase_1078_, lean_object* v_occurrence_1079_){
_start:
{
uint8_t v_phase_boxed_1080_; lean_object* v_res_1081_; 
v_phase_boxed_1080_ = lean_unbox(v_phase_1078_);
v_res_1081_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_1080_, v_occurrence_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1153_ = 1;
v___x_1154_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1155_ = l_Lean_registerTraceClass(v___x_1152_, v___x_1153_, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
return v_res_1157_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ElimDead(builtin);
}
#ifdef __cplusplus
}
#endif
