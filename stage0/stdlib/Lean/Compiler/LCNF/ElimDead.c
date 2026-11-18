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
size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((size_t)0ULL);
v___x_38_ = lean_usize_of_nat(v___x_35_);
v___x_39_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_args_33_, v___x_37_, v___x_38_, v_s_32_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* v_pu_40_, lean_object* v_s_41_, lean_object* v_args_42_){
_start:
{
uint8_t v_pu_boxed_43_; lean_object* v_res_44_; 
v_pu_boxed_43_ = lean_unbox(v_pu_40_);
v_res_44_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_boxed_43_, v_s_41_, v_args_42_);
lean_dec_ref(v_args_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(uint8_t v_pu_45_, lean_object* v_as_46_, size_t v_i_47_, size_t v_stop_48_, lean_object* v_b_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___redArg(v_as_46_, v_i_47_, v_stop_48_, v_b_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* v_pu_51_, lean_object* v_as_52_, lean_object* v_i_53_, lean_object* v_stop_54_, lean_object* v_b_55_){
_start:
{
uint8_t v_pu_boxed_56_; size_t v_i_boxed_57_; size_t v_stop_boxed_58_; lean_object* v_res_59_; 
v_pu_boxed_56_ = lean_unbox(v_pu_51_);
v_i_boxed_57_ = lean_unbox_usize(v_i_53_);
lean_dec(v_i_53_);
v_stop_boxed_58_ = lean_unbox_usize(v_stop_54_);
lean_dec(v_stop_54_);
v_res_59_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(v_pu_boxed_56_, v_as_52_, v_i_boxed_57_, v_stop_boxed_58_, v_b_55_);
lean_dec_ref(v_as_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(uint8_t v_pu_60_, lean_object* v_s_61_, lean_object* v_e_62_){
_start:
{
switch(lean_obj_tag(v_e_62_))
{
case 2:
{
lean_object* v_struct_63_; lean_object* v___x_64_; 
v_struct_63_ = lean_ctor_get(v_e_62_, 2);
lean_inc(v_struct_63_);
lean_dec_ref_known(v_e_62_, 3);
v___x_64_ = l_Lean_FVarIdSet_insert(v_s_61_, v_struct_63_);
return v___x_64_;
}
case 3:
{
lean_object* v_args_65_; lean_object* v___x_66_; 
v_args_65_ = lean_ctor_get(v_e_62_, 2);
lean_inc_ref(v_args_65_);
lean_dec_ref_known(v_e_62_, 3);
v___x_66_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_60_, v_s_61_, v_args_65_);
lean_dec_ref(v_args_65_);
return v___x_66_;
}
case 4:
{
lean_object* v_fvarId_67_; lean_object* v_args_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_fvarId_67_ = lean_ctor_get(v_e_62_, 0);
lean_inc(v_fvarId_67_);
v_args_68_ = lean_ctor_get(v_e_62_, 1);
lean_inc_ref(v_args_68_);
lean_dec_ref_known(v_e_62_, 2);
v___x_69_ = l_Lean_FVarIdSet_insert(v_s_61_, v_fvarId_67_);
v___x_70_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_60_, v___x_69_, v_args_68_);
lean_dec_ref(v_args_68_);
return v___x_70_;
}
case 5:
{
lean_object* v_args_71_; lean_object* v___x_72_; 
v_args_71_ = lean_ctor_get(v_e_62_, 1);
lean_inc_ref(v_args_71_);
lean_dec_ref_known(v_e_62_, 2);
v___x_72_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_60_, v_s_61_, v_args_71_);
lean_dec_ref(v_args_71_);
return v___x_72_;
}
case 6:
{
lean_object* v_var_73_; lean_object* v___x_74_; 
v_var_73_ = lean_ctor_get(v_e_62_, 1);
lean_inc(v_var_73_);
lean_dec_ref_known(v_e_62_, 2);
v___x_74_ = l_Lean_FVarIdSet_insert(v_s_61_, v_var_73_);
return v___x_74_;
}
case 7:
{
lean_object* v_var_75_; lean_object* v___x_76_; 
v_var_75_ = lean_ctor_get(v_e_62_, 1);
lean_inc(v_var_75_);
lean_dec_ref_known(v_e_62_, 2);
v___x_76_ = l_Lean_FVarIdSet_insert(v_s_61_, v_var_75_);
return v___x_76_;
}
case 8:
{
lean_object* v_var_77_; lean_object* v___x_78_; 
v_var_77_ = lean_ctor_get(v_e_62_, 2);
lean_inc(v_var_77_);
lean_dec_ref_known(v_e_62_, 3);
v___x_78_ = l_Lean_FVarIdSet_insert(v_s_61_, v_var_77_);
return v___x_78_;
}
case 9:
{
lean_object* v_args_79_; lean_object* v___x_80_; 
v_args_79_ = lean_ctor_get(v_e_62_, 1);
lean_inc_ref(v_args_79_);
lean_dec_ref_known(v_e_62_, 2);
v___x_80_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_60_, v_s_61_, v_args_79_);
lean_dec_ref(v_args_79_);
return v___x_80_;
}
case 10:
{
lean_object* v_args_81_; lean_object* v___x_82_; 
v_args_81_ = lean_ctor_get(v_e_62_, 1);
lean_inc_ref(v_args_81_);
lean_dec_ref_known(v_e_62_, 2);
v___x_82_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_60_, v_s_61_, v_args_81_);
lean_dec_ref(v_args_81_);
return v___x_82_;
}
case 11:
{
lean_object* v_var_83_; lean_object* v___x_84_; 
v_var_83_ = lean_ctor_get(v_e_62_, 1);
lean_inc(v_var_83_);
lean_dec_ref_known(v_e_62_, 2);
v___x_84_ = l_Lean_FVarIdSet_insert(v_s_61_, v_var_83_);
return v___x_84_;
}
case 12:
{
lean_object* v_var_85_; lean_object* v_args_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_var_85_ = lean_ctor_get(v_e_62_, 0);
lean_inc(v_var_85_);
v_args_86_ = lean_ctor_get(v_e_62_, 2);
lean_inc_ref(v_args_86_);
lean_dec_ref_known(v_e_62_, 3);
v___x_87_ = l_Lean_FVarIdSet_insert(v_s_61_, v_var_85_);
v___x_88_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArgs(v_pu_60_, v___x_87_, v_args_86_);
lean_dec_ref(v_args_86_);
return v___x_88_;
}
case 13:
{
lean_object* v_fvarId_89_; lean_object* v___x_90_; 
v_fvarId_89_ = lean_ctor_get(v_e_62_, 1);
lean_inc(v_fvarId_89_);
lean_dec_ref_known(v_e_62_, 2);
v___x_90_ = l_Lean_FVarIdSet_insert(v_s_61_, v_fvarId_89_);
return v___x_90_;
}
case 14:
{
lean_object* v_fvarId_91_; lean_object* v___x_92_; 
v_fvarId_91_ = lean_ctor_get(v_e_62_, 0);
lean_inc(v_fvarId_91_);
lean_dec_ref_known(v_e_62_, 1);
v___x_92_ = l_Lean_FVarIdSet_insert(v_s_61_, v_fvarId_91_);
return v___x_92_;
}
case 15:
{
lean_object* v_fvarId_93_; lean_object* v___x_94_; 
v_fvarId_93_ = lean_ctor_get(v_e_62_, 0);
lean_inc(v_fvarId_93_);
lean_dec_ref_known(v_e_62_, 1);
v___x_94_ = l_Lean_FVarIdSet_insert(v_s_61_, v_fvarId_93_);
return v___x_94_;
}
default: 
{
lean_dec(v_e_62_);
return v_s_61_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue___boxed(lean_object* v_pu_95_, lean_object* v_s_96_, lean_object* v_e_97_){
_start:
{
uint8_t v_pu_boxed_98_; lean_object* v_res_99_; 
v_pu_boxed_98_ = lean_unbox(v_pu_95_);
v_res_99_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_boxed_98_, v_s_96_, v_e_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(lean_object* v_arg_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_103_ = lean_st_ref_take(v_a_101_);
v___x_104_ = lean_box(0);
v___x_105_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_103_, v_arg_100_);
v___x_106_ = lean_st_ref_put(v_a_101_, v___x_105_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg___boxed(lean_object* v_arg_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___redArg(v_arg_108_, v_a_109_);
lean_dec(v_a_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(uint8_t v_pu_112_, lean_object* v_arg_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = lean_st_ref_take(v_a_114_);
v___x_121_ = lean_box(0);
v___x_122_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_120_, v_arg_113_);
v___x_123_ = lean_st_ref_put(v_a_114_, v___x_122_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM___boxed(lean_object* v_pu_125_, lean_object* v_arg_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
uint8_t v_pu_boxed_133_; lean_object* v_res_134_; 
v_pu_boxed_133_ = lean_unbox(v_pu_125_);
v_res_134_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectArgM(v_pu_boxed_133_, v_arg_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(uint8_t v_pu_135_, lean_object* v_e_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = lean_st_ref_take(v_a_137_);
v___x_140_ = lean_box(0);
v___x_141_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_135_, v___x_139_, v_e_136_);
v___x_142_ = lean_st_ref_put(v_a_137_, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_140_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg___boxed(lean_object* v_pu_144_, lean_object* v_e_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
uint8_t v_pu_boxed_148_; lean_object* v_res_149_; 
v_pu_boxed_148_ = lean_unbox(v_pu_144_);
v_res_149_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___redArg(v_pu_boxed_148_, v_e_145_, v_a_146_);
lean_dec(v_a_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(uint8_t v_pu_150_, lean_object* v_e_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = lean_st_ref_take(v_a_152_);
v___x_159_ = lean_box(0);
v___x_160_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_150_, v___x_158_, v_e_151_);
v___x_161_ = lean_st_ref_put(v_a_152_, v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM___boxed(lean_object* v_pu_163_, lean_object* v_e_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
uint8_t v_pu_boxed_171_; lean_object* v_res_172_; 
v_pu_boxed_171_ = lean_unbox(v_pu_163_);
v_res_172_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLetValueM(v_pu_boxed_171_, v_e_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(lean_object* v_fvarId_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = lean_st_ref_take(v_a_174_);
v___x_177_ = lean_box(0);
v___x_178_ = l_Lean_FVarIdSet_insert(v___x_176_, v_fvarId_173_);
v___x_179_ = lean_st_ref_put(v_a_174_, v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg___boxed(lean_object* v_fvarId_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___redArg(v_fvarId_181_, v_a_182_);
lean_dec(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(lean_object* v_fvarId_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = lean_st_ref_take(v_a_186_);
v___x_193_ = lean_box(0);
v___x_194_ = l_Lean_FVarIdSet_insert(v___x_192_, v_fvarId_185_);
v___x_195_ = lean_st_ref_put(v_a_186_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM___boxed(lean_object* v_fvarId_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectFVarM(v_fvarId_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(uint8_t v_pu_205_, lean_object* v_val_206_){
_start:
{
if (v_pu_205_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = 1;
return v___x_207_;
}
else
{
switch(lean_obj_tag(v_val_206_))
{
case 4:
{
uint8_t v___x_208_; 
v___x_208_ = 0;
return v___x_208_;
}
case 9:
{
lean_object* v_args_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_args_209_ = lean_ctor_get(v_val_206_, 1);
v___x_210_ = lean_array_get_size(v_args_209_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_nat_dec_eq(v___x_210_, v___x_211_);
return v___x_212_;
}
default: 
{
uint8_t v___x_213_; 
v___x_213_ = 1;
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim___boxed(lean_object* v_pu_214_, lean_object* v_val_215_){
_start:
{
uint8_t v_pu_boxed_216_; uint8_t v_res_217_; lean_object* v_r_218_; 
v_pu_boxed_216_ = lean_unbox(v_pu_214_);
v_res_217_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_boxed_216_, v_val_215_);
lean_dec(v_val_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(lean_object* v_as_219_, size_t v_i_220_, size_t v_stop_221_, lean_object* v_b_222_, lean_object* v___y_223_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = lean_usize_dec_eq(v_i_220_, v_stop_221_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; size_t v___x_231_; size_t v___x_232_; 
v___x_226_ = lean_array_uget_borrowed(v_as_219_, v_i_220_);
v___x_227_ = lean_st_ref_take(v___y_223_);
v___x_228_ = lean_box(0);
lean_inc(v___x_226_);
v___x_229_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_227_, v___x_226_);
v___x_230_ = lean_st_ref_put(v___y_223_, v___x_229_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_i_220_, v___x_231_);
v_i_220_ = v___x_232_;
v_b_222_ = v___x_228_;
goto _start;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_b_222_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg___boxed(lean_object* v_as_235_, lean_object* v_i_236_, lean_object* v_stop_237_, lean_object* v_b_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
size_t v_i_boxed_241_; size_t v_stop_boxed_242_; lean_object* v_res_243_; 
v_i_boxed_241_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_stop_boxed_242_ = lean_unbox_usize(v_stop_237_);
lean_dec(v_stop_237_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_235_, v_i_boxed_241_, v_stop_boxed_242_, v_b_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v_as_235_);
return v_res_243_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(lean_object* v_k_244_, lean_object* v_t_245_){
_start:
{
if (lean_obj_tag(v_t_245_) == 0)
{
lean_object* v_k_246_; lean_object* v_l_247_; lean_object* v_r_248_; uint8_t v___x_249_; 
v_k_246_ = lean_ctor_get(v_t_245_, 1);
v_l_247_ = lean_ctor_get(v_t_245_, 3);
v_r_248_ = lean_ctor_get(v_t_245_, 4);
v___x_249_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_244_, v_k_246_);
switch(v___x_249_)
{
case 0:
{
v_t_245_ = v_l_247_;
goto _start;
}
case 1:
{
uint8_t v___x_251_; 
v___x_251_ = 1;
return v___x_251_;
}
default: 
{
v_t_245_ = v_r_248_;
goto _start;
}
}
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg___boxed(lean_object* v_k_254_, lean_object* v_t_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_254_, v_t_255_);
lean_dec(v_t_255_);
lean_dec(v_k_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(uint8_t v_pu_258_, lean_object* v_i_259_, lean_object* v_as_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_array_get_size(v_as_260_);
v___x_268_ = lean_nat_dec_lt(v_i_259_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_dec(v_i_259_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_as_260_);
return v___x_269_;
}
else
{
lean_object* v_a_270_; lean_object* v___y_272_; 
v_a_270_ = lean_array_fget_borrowed(v_as_260_, v_i_259_);
switch(lean_obj_tag(v_a_270_))
{
case 0:
{
lean_object* v_code_294_; 
v_code_294_ = lean_ctor_get(v_a_270_, 2);
lean_inc_ref(v_code_294_);
v___y_272_ = v_code_294_;
goto v___jp_271_;
}
case 1:
{
lean_object* v_code_295_; 
v_code_295_ = lean_ctor_get(v_a_270_, 1);
lean_inc_ref(v_code_295_);
v___y_272_ = v_code_295_;
goto v___jp_271_;
}
default: 
{
lean_object* v_code_296_; 
v_code_296_ = lean_ctor_get(v_a_270_, 0);
lean_inc_ref(v_code_296_);
v___y_272_ = v_code_296_;
goto v___jp_271_;
}
}
v___jp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_258_, v___y_272_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; size_t v___x_276_; size_t v___x_277_; uint8_t v___x_278_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
lean_inc(v_a_270_);
v___x_275_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_270_, v_a_274_);
v___x_276_ = lean_ptr_addr(v_a_270_);
v___x_277_ = lean_ptr_addr(v___x_275_);
v___x_278_ = lean_usize_dec_eq(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_i_259_, v___x_279_);
v___x_281_ = lean_array_fset(v_as_260_, v_i_259_, v___x_275_);
lean_dec(v_i_259_);
v_i_259_ = v___x_280_;
v_as_260_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___x_275_);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_add(v_i_259_, v___x_283_);
lean_dec(v_i_259_);
v_i_259_ = v___x_284_;
goto _start;
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_as_260_);
lean_dec(v_i_259_);
v_a_286_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_273_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_273_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(uint8_t v_pu_297_, lean_object* v_code_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
switch(lean_obj_tag(v_code_298_))
{
case 0:
{
lean_object* v_decl_305_; lean_object* v_k_306_; lean_object* v___x_307_; 
v_decl_305_ = lean_ctor_get(v_code_298_, 0);
v_k_306_ = lean_ctor_get(v_code_298_, 1);
lean_inc_ref(v_k_306_);
v___x_307_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_306_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_356_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_356_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_356_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_356_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_fvarId_313_; lean_object* v_value_314_; uint8_t v___x_337_; 
v___x_312_ = lean_st_ref_get(v_a_299_);
v_fvarId_313_ = lean_ctor_get(v_decl_305_, 0);
v_value_314_ = lean_ctor_get(v_decl_305_, 3);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_313_, v___x_312_);
lean_dec(v___x_312_);
if (v___x_337_ == 0)
{
uint8_t v___x_338_; 
v___x_338_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_LetValue_safeToElim(v_pu_297_, v_value_314_);
if (v___x_338_ == 0)
{
goto v___jp_315_;
}
else
{
lean_object* v___x_339_; 
lean_inc_ref(v_decl_305_);
lean_del_object(v___x_310_);
lean_dec_ref_known(v_code_298_, 2);
v___x_339_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v_pu_297_, v_decl_305_, v_a_301_);
lean_dec_ref(v_decl_305_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; 
v_unused_347_ = lean_ctor_get(v___x_339_, 0);
lean_dec(v_unused_347_);
v___x_341_ = v___x_339_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_dec(v___x_339_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v_a_308_);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_308_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_308_);
v_a_348_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_339_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_339_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
goto v___jp_315_;
}
v___jp_315_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; size_t v___x_319_; size_t v___x_320_; uint8_t v___x_321_; 
v___x_316_ = lean_st_ref_take(v_a_299_);
lean_inc(v_value_314_);
v___x_317_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsLetValue(v_pu_297_, v___x_316_, v_value_314_);
v___x_318_ = lean_st_ref_put(v_a_299_, v___x_317_);
v___x_319_ = lean_ptr_addr(v_k_306_);
v___x_320_ = lean_ptr_addr(v_a_308_);
v___x_321_ = lean_usize_dec_eq(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
lean_inc_ref(v_decl_305_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_332_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_333_);
v___x_323_ = v_code_298_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_code_298_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v_a_308_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_decl_305_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_a_308_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_326_);
v___x_328_ = v___x_310_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
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
else
{
lean_object* v___x_335_; 
lean_dec(v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v_code_298_);
v___x_335_ = v___x_310_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_code_298_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 2);
return v___x_307_;
}
}
case 1:
{
lean_object* v_decl_357_; lean_object* v_k_358_; lean_object* v___x_359_; 
v_decl_357_ = lean_ctor_get(v_code_298_, 0);
v_k_358_ = lean_ctor_get(v_code_298_, 1);
lean_inc_ref(v_k_358_);
v___x_359_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_358_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v_fvarId_362_; uint8_t v___x_363_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_st_ref_get(v_a_299_);
v_fvarId_362_ = lean_ctor_get(v_decl_357_, 0);
v___x_363_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_362_, v___x_361_);
lean_dec(v___x_361_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; lean_object* v___x_365_; 
lean_inc_ref(v_decl_357_);
lean_dec_ref_known(v_code_298_, 2);
v___x_364_ = 1;
v___x_365_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_297_, v_decl_357_, v___x_364_, v_a_301_);
lean_dec_ref(v_decl_357_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_373_);
v___x_367_ = v___x_365_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_365_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v_a_360_);
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_360_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_a_360_);
v_a_374_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_365_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_365_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v___x_382_; 
lean_inc_ref(v_decl_357_);
v___x_382_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_297_, v_decl_357_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_420_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_420_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_420_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_420_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
size_t v___x_387_; size_t v___x_388_; uint8_t v___x_389_; 
v___x_387_ = lean_ptr_addr(v_k_358_);
v___x_388_ = lean_ptr_addr(v_a_360_);
v___x_389_ = lean_usize_dec_eq(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v_isSharedCheck_399_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_400_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_401_);
v___x_391_ = v_code_298_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_dec(v_code_298_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v_a_360_);
lean_ctor_set(v___x_391_, 0, v_a_383_);
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_383_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_a_360_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_394_);
v___x_396_ = v___x_385_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
size_t v___x_402_; size_t v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_ptr_addr(v_decl_357_);
v___x_403_ = lean_ptr_addr(v_a_383_);
v___x_404_ = lean_usize_dec_eq(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_414_; 
v_isSharedCheck_414_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_415_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_416_);
v___x_406_ = v_code_298_;
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_code_298_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_a_360_);
lean_ctor_set(v___x_406_, 0, v_a_383_);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_383_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_a_360_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_409_);
v___x_411_ = v___x_385_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v___x_418_; 
lean_dec(v_a_383_);
lean_dec(v_a_360_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v_code_298_);
v___x_418_ = v___x_385_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_code_298_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_a_360_);
lean_dec_ref_known(v_code_298_, 2);
v_a_421_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_382_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_382_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 2);
return v___x_359_;
}
}
case 2:
{
lean_object* v_decl_429_; lean_object* v_k_430_; lean_object* v___x_431_; 
v_decl_429_ = lean_ctor_get(v_code_298_, 0);
v_k_430_ = lean_ctor_get(v_code_298_, 1);
lean_inc_ref(v_k_430_);
v___x_431_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_430_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; lean_object* v_fvarId_434_; uint8_t v___x_435_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
v___x_433_ = lean_st_ref_get(v_a_299_);
v_fvarId_434_ = lean_ctor_get(v_decl_429_, 0);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_434_, v___x_433_);
lean_dec(v___x_433_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; lean_object* v___x_437_; 
lean_inc_ref(v_decl_429_);
lean_dec_ref_known(v_code_298_, 2);
v___x_436_ = 1;
v___x_437_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v_pu_297_, v_decl_429_, v___x_436_, v_a_301_);
lean_dec_ref(v_decl_429_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_445_);
v___x_439_ = v___x_437_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_dec(v___x_437_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_a_432_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_432_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_a_432_);
v_a_446_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_437_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_437_);
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
else
{
lean_object* v___x_454_; 
lean_inc_ref(v_decl_429_);
v___x_454_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_297_, v_decl_429_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_492_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_492_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_492_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_492_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_ptr_addr(v_k_430_);
v___x_460_ = lean_ptr_addr(v_a_432_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_471_; 
v_isSharedCheck_471_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_472_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_473_);
v___x_463_ = v_code_298_;
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_code_298_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_a_432_);
lean_ctor_set(v___x_463_, 0, v_a_455_);
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_455_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_a_432_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_466_);
v___x_468_ = v___x_457_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
size_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_ptr_addr(v_decl_429_);
v___x_475_ = lean_ptr_addr(v_a_455_);
v___x_476_ = lean_usize_dec_eq(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_486_; 
v_isSharedCheck_486_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_487_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_488_);
v___x_478_ = v_code_298_;
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
else
{
lean_dec(v_code_298_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_a_432_);
lean_ctor_set(v___x_478_, 0, v_a_455_);
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_455_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_a_432_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_481_);
v___x_483_ = v___x_457_;
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
}
else
{
lean_object* v___x_490_; 
lean_dec(v_a_455_);
lean_dec(v_a_432_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v_code_298_);
v___x_490_ = v___x_457_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_code_298_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_a_432_);
lean_dec_ref_known(v_code_298_, 2);
v_a_493_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_454_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_454_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 2);
return v___x_431_;
}
}
case 3:
{
lean_object* v_fvarId_501_; lean_object* v_args_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_fvarId_501_ = lean_ctor_get(v_code_298_, 0);
v_args_502_ = lean_ctor_get(v_code_298_, 1);
v___x_503_ = lean_st_ref_take(v_a_299_);
lean_inc(v_fvarId_501_);
v___x_504_ = l_Lean_FVarIdSet_insert(v___x_503_, v_fvarId_501_);
v___x_505_ = lean_st_ref_put(v_a_299_, v___x_504_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_array_get_size(v_args_502_);
v___x_508_ = lean_nat_dec_lt(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_code_298_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_510_ = lean_box(0);
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_507_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_args_502_, v___x_511_, v___x_512_, v___x_510_, v_a_299_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_521_);
v___x_515_ = v___x_513_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_dec(v___x_513_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v_code_298_);
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_code_298_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref_known(v_code_298_, 2);
v_a_522_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
case 4:
{
lean_object* v_cases_530_; lean_object* v_typeName_531_; lean_object* v_resultType_532_; lean_object* v_discr_533_; lean_object* v_alts_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_576_; 
v_cases_530_ = lean_ctor_get(v_code_298_, 0);
lean_inc_ref(v_cases_530_);
v_typeName_531_ = lean_ctor_get(v_cases_530_, 0);
v_resultType_532_ = lean_ctor_get(v_cases_530_, 1);
v_discr_533_ = lean_ctor_get(v_cases_530_, 2);
v_alts_534_ = lean_ctor_get(v_cases_530_, 3);
v_isSharedCheck_576_ = !lean_is_exclusive(v_cases_530_);
if (v_isSharedCheck_576_ == 0)
{
v___x_536_ = v_cases_530_;
v_isShared_537_ = v_isSharedCheck_576_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_alts_534_);
lean_inc(v_discr_533_);
lean_inc(v_resultType_532_);
lean_inc(v_typeName_531_);
lean_dec(v_cases_530_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_576_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_534_);
v___x_539_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_297_, v___x_538_, v_alts_534_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_567_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_567_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_567_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_567_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; size_t v___x_547_; size_t v___x_548_; uint8_t v___x_549_; 
v___x_544_ = lean_st_ref_take(v_a_299_);
lean_inc(v_discr_533_);
v___x_545_ = l_Lean_FVarIdSet_insert(v___x_544_, v_discr_533_);
v___x_546_ = lean_st_ref_put(v_a_299_, v___x_545_);
v___x_547_ = lean_ptr_addr(v_alts_534_);
lean_dec_ref(v_alts_534_);
v___x_548_ = lean_ptr_addr(v_a_540_);
v___x_549_ = lean_usize_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_562_; 
v_isSharedCheck_562_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_563_);
v___x_551_ = v_code_298_;
v_isShared_552_ = v_isSharedCheck_562_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_code_298_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_562_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 3, v_a_540_);
v___x_554_ = v___x_536_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_typeName_531_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_resultType_532_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_discr_533_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_a_540_);
v___x_554_ = v_reuseFailAlloc_561_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_556_);
v___x_558_ = v___x_542_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
else
{
lean_object* v___x_565_; 
lean_dec(v_a_540_);
lean_del_object(v___x_536_);
lean_dec(v_discr_533_);
lean_dec_ref(v_resultType_532_);
lean_dec(v_typeName_531_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_code_298_);
v___x_565_ = v___x_542_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_code_298_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_del_object(v___x_536_);
lean_dec_ref(v_alts_534_);
lean_dec(v_discr_533_);
lean_dec_ref(v_resultType_532_);
lean_dec(v_typeName_531_);
lean_dec_ref_known(v_code_298_, 1);
v_a_568_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_539_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_539_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_fvarId_577_ = lean_ctor_get(v_code_298_, 0);
v___x_578_ = lean_st_ref_take(v_a_299_);
lean_inc(v_fvarId_577_);
v___x_579_ = l_Lean_FVarIdSet_insert(v___x_578_, v_fvarId_577_);
v___x_580_ = lean_st_ref_put(v_a_299_, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_code_298_);
return v___x_581_;
}
case 6:
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_code_298_);
return v___x_582_;
}
case 7:
{
lean_object* v_fvarId_583_; lean_object* v_i_584_; lean_object* v_y_585_; lean_object* v_k_586_; lean_object* v___x_587_; 
v_fvarId_583_ = lean_ctor_get(v_code_298_, 0);
v_i_584_ = lean_ctor_get(v_code_298_, 1);
v_y_585_ = lean_ctor_get(v_code_298_, 2);
v_k_586_ = lean_ctor_get(v_code_298_, 3);
lean_inc_ref(v_k_586_);
v___x_587_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_586_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_620_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_620_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_620_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_st_ref_get(v_a_299_);
v___x_593_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_583_, v___x_592_);
lean_dec(v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_595_; 
lean_dec_ref_known(v_code_298_, 4);
if (v_isShared_591_ == 0)
{
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_588_);
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
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; size_t v___x_600_; size_t v___x_601_; uint8_t v___x_602_; 
v___x_597_ = lean_st_ref_take(v_a_299_);
lean_inc(v_y_585_);
v___x_598_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_collectLocalDeclsArg___redArg(v___x_597_, v_y_585_);
v___x_599_ = lean_st_ref_put(v_a_299_, v___x_598_);
v___x_600_ = lean_ptr_addr(v_k_586_);
v___x_601_ = lean_ptr_addr(v_a_588_);
v___x_602_ = lean_usize_dec_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_612_; 
lean_inc(v_y_585_);
lean_inc(v_i_584_);
lean_inc(v_fvarId_583_);
v_isSharedCheck_612_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; 
v_unused_613_ = lean_ctor_get(v_code_298_, 3);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_code_298_, 2);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_616_);
v___x_604_ = v_code_298_;
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_code_298_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 3, v_a_588_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_fvarId_583_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_i_584_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_y_585_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_a_588_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_607_);
v___x_609_ = v___x_590_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v_a_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_code_298_);
v___x_618_ = v___x_590_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_code_298_);
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
else
{
lean_dec_ref_known(v_code_298_, 4);
return v___x_587_;
}
}
case 8:
{
lean_object* v_fvarId_621_; lean_object* v_i_622_; lean_object* v_y_623_; lean_object* v_k_624_; lean_object* v___x_625_; 
v_fvarId_621_ = lean_ctor_get(v_code_298_, 0);
v_i_622_ = lean_ctor_get(v_code_298_, 1);
v_y_623_ = lean_ctor_get(v_code_298_, 2);
v_k_624_ = lean_ctor_get(v_code_298_, 3);
lean_inc_ref(v_k_624_);
v___x_625_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_624_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_658_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_658_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_658_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_658_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_st_ref_get(v_a_299_);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_621_, v___x_630_);
lean_dec(v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_633_; 
lean_dec_ref_known(v_code_298_, 4);
if (v_isShared_629_ == 0)
{
v___x_633_ = v___x_628_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_626_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; size_t v___x_638_; size_t v___x_639_; uint8_t v___x_640_; 
v___x_635_ = lean_st_ref_take(v_a_299_);
lean_inc(v_y_623_);
v___x_636_ = l_Lean_FVarIdSet_insert(v___x_635_, v_y_623_);
v___x_637_ = lean_st_ref_put(v_a_299_, v___x_636_);
v___x_638_ = lean_ptr_addr(v_k_624_);
v___x_639_ = lean_ptr_addr(v_a_626_);
v___x_640_ = lean_usize_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_650_; 
lean_inc(v_y_623_);
lean_inc(v_i_622_);
lean_inc(v_fvarId_621_);
v_isSharedCheck_650_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; 
v_unused_651_ = lean_ctor_get(v_code_298_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_code_298_, 2);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_654_);
v___x_642_ = v_code_298_;
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
else
{
lean_dec(v_code_298_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_650_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 3, v_a_626_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_fvarId_621_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_i_622_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_y_623_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_a_626_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_645_);
v___x_647_ = v___x_628_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v___x_656_; 
lean_dec(v_a_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_code_298_);
v___x_656_ = v___x_628_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_code_298_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 4);
return v___x_625_;
}
}
case 9:
{
lean_object* v_fvarId_659_; lean_object* v_i_660_; lean_object* v_offset_661_; lean_object* v_y_662_; lean_object* v_ty_663_; lean_object* v_k_664_; lean_object* v___x_665_; 
v_fvarId_659_ = lean_ctor_get(v_code_298_, 0);
v_i_660_ = lean_ctor_get(v_code_298_, 1);
v_offset_661_ = lean_ctor_get(v_code_298_, 2);
v_y_662_ = lean_ctor_get(v_code_298_, 3);
v_ty_663_ = lean_ctor_get(v_code_298_, 4);
v_k_664_ = lean_ctor_get(v_code_298_, 5);
lean_inc_ref(v_k_664_);
v___x_665_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_664_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_700_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_700_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_700_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_700_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = lean_st_ref_get(v_a_299_);
v___x_671_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_fvarId_659_, v___x_670_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref_known(v_code_298_, 6);
if (v_isShared_669_ == 0)
{
v___x_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_666_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; uint8_t v___x_680_; 
v___x_675_ = lean_st_ref_take(v_a_299_);
lean_inc(v_y_662_);
v___x_676_ = l_Lean_FVarIdSet_insert(v___x_675_, v_y_662_);
v___x_677_ = lean_st_ref_put(v_a_299_, v___x_676_);
v___x_678_ = lean_ptr_addr(v_k_664_);
v___x_679_ = lean_ptr_addr(v_a_666_);
v___x_680_ = lean_usize_dec_eq(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_690_; 
lean_inc_ref(v_ty_663_);
lean_inc(v_y_662_);
lean_inc(v_offset_661_);
lean_inc(v_i_660_);
lean_inc(v_fvarId_659_);
v_isSharedCheck_690_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; lean_object* v_unused_695_; lean_object* v_unused_696_; 
v_unused_691_ = lean_ctor_get(v_code_298_, 5);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_code_298_, 4);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v_code_298_, 3);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_code_298_, 2);
lean_dec(v_unused_694_);
v_unused_695_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_695_);
v_unused_696_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_696_);
v___x_682_ = v_code_298_;
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
else
{
lean_dec(v_code_298_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 5, v_a_666_);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fvarId_659_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_i_660_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_offset_661_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_y_662_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_ty_663_);
lean_ctor_set(v_reuseFailAlloc_689_, 5, v_a_666_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_685_);
v___x_687_ = v___x_668_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v___x_698_; 
lean_dec(v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_code_298_);
v___x_698_ = v___x_668_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_code_298_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 6);
return v___x_665_;
}
}
case 10:
{
lean_object* v_fvarId_701_; lean_object* v_cidx_702_; lean_object* v_k_703_; lean_object* v___x_704_; 
v_fvarId_701_ = lean_ctor_get(v_code_298_, 0);
v_cidx_702_ = lean_ctor_get(v_code_298_, 1);
v_k_703_ = lean_ctor_get(v_code_298_, 2);
lean_inc_ref(v_k_703_);
v___x_704_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_703_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_731_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_731_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_731_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_731_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; size_t v___x_712_; size_t v___x_713_; uint8_t v___x_714_; 
v___x_709_ = lean_st_ref_take(v_a_299_);
lean_inc(v_fvarId_701_);
v___x_710_ = l_Lean_FVarIdSet_insert(v___x_709_, v_fvarId_701_);
v___x_711_ = lean_st_ref_put(v_a_299_, v___x_710_);
v___x_712_ = lean_ptr_addr(v_k_703_);
v___x_713_ = lean_ptr_addr(v_a_705_);
v___x_714_ = lean_usize_dec_eq(v___x_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
lean_inc(v_cidx_702_);
lean_inc(v_fvarId_701_);
v_isSharedCheck_724_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; 
v_unused_725_ = lean_ctor_get(v_code_298_, 2);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_727_);
v___x_716_ = v_code_298_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_dec(v_code_298_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v_a_705_);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fvarId_701_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_cidx_702_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_a_705_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_719_);
v___x_721_ = v___x_707_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v___x_729_; 
lean_dec(v_a_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_code_298_);
v___x_729_ = v___x_707_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_code_298_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 3);
return v___x_704_;
}
}
case 11:
{
lean_object* v_fvarId_732_; lean_object* v_n_733_; uint8_t v_check_734_; uint8_t v_persistent_735_; lean_object* v_k_736_; lean_object* v___x_737_; 
v_fvarId_732_ = lean_ctor_get(v_code_298_, 0);
v_n_733_ = lean_ctor_get(v_code_298_, 1);
v_check_734_ = lean_ctor_get_uint8(v_code_298_, sizeof(void*)*3);
v_persistent_735_ = lean_ctor_get_uint8(v_code_298_, sizeof(void*)*3 + 1);
v_k_736_ = lean_ctor_get(v_code_298_, 2);
lean_inc_ref(v_k_736_);
v___x_737_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_736_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_764_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_764_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_764_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_764_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; size_t v___x_745_; size_t v___x_746_; uint8_t v___x_747_; 
v___x_742_ = lean_st_ref_take(v_a_299_);
lean_inc(v_fvarId_732_);
v___x_743_ = l_Lean_FVarIdSet_insert(v___x_742_, v_fvarId_732_);
v___x_744_ = lean_st_ref_put(v_a_299_, v___x_743_);
v___x_745_ = lean_ptr_addr(v_k_736_);
v___x_746_ = lean_ptr_addr(v_a_738_);
v___x_747_ = lean_usize_dec_eq(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_757_; 
lean_inc(v_n_733_);
lean_inc(v_fvarId_732_);
v_isSharedCheck_757_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; 
v_unused_758_ = lean_ctor_get(v_code_298_, 2);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_760_);
v___x_749_ = v_code_298_;
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_code_298_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 2, v_a_738_);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_fvarId_732_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_n_733_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_a_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*3, v_check_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*3 + 1, v_persistent_735_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_752_);
v___x_754_ = v___x_740_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v___x_762_; 
lean_dec(v_a_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_code_298_);
v___x_762_ = v___x_740_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_code_298_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 3);
return v___x_737_;
}
}
case 12:
{
lean_object* v_fvarId_765_; lean_object* v_n_766_; uint8_t v_check_767_; uint8_t v_persistent_768_; lean_object* v_objs_x3f_769_; lean_object* v_k_770_; lean_object* v___x_771_; 
v_fvarId_765_ = lean_ctor_get(v_code_298_, 0);
v_n_766_ = lean_ctor_get(v_code_298_, 1);
v_check_767_ = lean_ctor_get_uint8(v_code_298_, sizeof(void*)*4);
v_persistent_768_ = lean_ctor_get_uint8(v_code_298_, sizeof(void*)*4 + 1);
v_objs_x3f_769_ = lean_ctor_get(v_code_298_, 2);
v_k_770_ = lean_ctor_get(v_code_298_, 3);
lean_inc_ref(v_k_770_);
v___x_771_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_770_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_799_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_799_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_799_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_799_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; size_t v___x_779_; size_t v___x_780_; uint8_t v___x_781_; 
v___x_776_ = lean_st_ref_take(v_a_299_);
lean_inc(v_fvarId_765_);
v___x_777_ = l_Lean_FVarIdSet_insert(v___x_776_, v_fvarId_765_);
v___x_778_ = lean_st_ref_put(v_a_299_, v___x_777_);
v___x_779_ = lean_ptr_addr(v_k_770_);
v___x_780_ = lean_ptr_addr(v_a_772_);
v___x_781_ = lean_usize_dec_eq(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_objs_x3f_769_);
lean_inc(v_n_766_);
lean_inc(v_fvarId_765_);
v_isSharedCheck_791_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_792_ = lean_ctor_get(v_code_298_, 3);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_code_298_, 2);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_795_);
v___x_783_ = v_code_298_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_code_298_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 3, v_a_772_);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fvarId_765_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_n_766_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_objs_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_a_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_790_, sizeof(void*)*4, v_check_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_790_, sizeof(void*)*4 + 1, v_persistent_768_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_786_);
v___x_788_ = v___x_774_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_797_; 
lean_dec(v_a_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_code_298_);
v___x_797_ = v___x_774_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_code_298_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 4);
return v___x_771_;
}
}
default: 
{
lean_object* v_fvarId_800_; lean_object* v_k_801_; lean_object* v___x_802_; 
v_fvarId_800_ = lean_ctor_get(v_code_298_, 0);
v_k_801_ = lean_ctor_get(v_code_298_, 1);
lean_inc_ref(v_k_801_);
v___x_802_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_297_, v_k_801_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_828_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_828_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_828_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_828_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; uint8_t v___x_812_; 
v___x_807_ = lean_st_ref_take(v_a_299_);
lean_inc(v_fvarId_800_);
v___x_808_ = l_Lean_FVarIdSet_insert(v___x_807_, v_fvarId_800_);
v___x_809_ = lean_st_ref_put(v_a_299_, v___x_808_);
v___x_810_ = lean_ptr_addr(v_k_801_);
v___x_811_ = lean_ptr_addr(v_a_803_);
v___x_812_ = lean_usize_dec_eq(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_822_; 
lean_inc(v_fvarId_800_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_code_298_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; 
v_unused_823_ = lean_ctor_get(v_code_298_, 1);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_code_298_, 0);
lean_dec(v_unused_824_);
v___x_814_ = v_code_298_;
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
else
{
lean_dec(v_code_298_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_a_803_);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_fvarId_800_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_a_803_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_817_);
v___x_819_ = v___x_805_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
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
else
{
lean_object* v___x_826_; 
lean_dec(v_a_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_code_298_);
v___x_826_ = v___x_805_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_code_298_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_298_, 2);
return v___x_802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(uint8_t v_pu_829_, lean_object* v_funDecl_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_params_837_; lean_object* v_type_838_; lean_object* v_value_839_; lean_object* v___x_840_; 
v_params_837_ = lean_ctor_get(v_funDecl_830_, 2);
lean_inc_ref(v_params_837_);
v_type_838_ = lean_ctor_get(v_funDecl_830_, 3);
lean_inc_ref(v_type_838_);
v_value_839_ = lean_ctor_get(v_funDecl_830_, 4);
lean_inc_ref(v_value_839_);
v___x_840_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_829_, v_value_839_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_829_, v_funDecl_830_, v_type_838_, v_params_837_, v_a_841_, v_a_833_);
return v___x_842_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_type_838_);
lean_dec_ref(v_params_837_);
lean_dec_ref(v_funDecl_830_);
v_a_843_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_840_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_840_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl___boxed(lean_object* v_pu_851_, lean_object* v_funDecl_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v_pu_boxed_859_; lean_object* v_res_860_; 
v_pu_boxed_859_ = lean_unbox(v_pu_851_);
v_res_860_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_visitFunDecl(v_pu_boxed_859_, v_funDecl_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3___boxed(lean_object* v_pu_861_, lean_object* v_i_862_, lean_object* v_as_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_pu_boxed_870_; lean_object* v_res_871_; 
v_pu_boxed_870_ = lean_unbox(v_pu_861_);
v_res_871_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__3(v_pu_boxed_870_, v_i_862_, v_as_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* v_pu_872_, lean_object* v_code_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
uint8_t v_pu_boxed_880_; lean_object* v_res_881_; 
v_pu_boxed_880_ = lean_unbox(v_pu_872_);
v_res_881_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_boxed_880_, v_code_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
return v_res_881_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(lean_object* v_00_u03b2_882_, lean_object* v_k_883_, lean_object* v_t_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___redArg(v_k_883_, v_t_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1___boxed(lean_object* v_00_u03b2_886_, lean_object* v_k_887_, lean_object* v_t_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__1(v_00_u03b2_886_, v_k_887_, v_t_888_);
lean_dec(v_t_888_);
lean_dec(v_k_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(uint8_t v_pu_891_, lean_object* v_as_892_, size_t v_i_893_, size_t v_stop_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___redArg(v_as_892_, v_i_893_, v_stop_894_, v_b_895_, v___y_896_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2___boxed(lean_object* v_pu_903_, lean_object* v_as_904_, lean_object* v_i_905_, lean_object* v_stop_906_, lean_object* v_b_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
uint8_t v_pu_boxed_914_; size_t v_i_boxed_915_; size_t v_stop_boxed_916_; lean_object* v_res_917_; 
v_pu_boxed_914_ = lean_unbox(v_pu_903_);
v_i_boxed_915_ = lean_unbox_usize(v_i_905_);
lean_dec(v_i_905_);
v_stop_boxed_916_ = lean_unbox_usize(v_stop_906_);
lean_dec(v_stop_906_);
v_res_917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead_spec__2(v_pu_boxed_914_, v_as_904_, v_i_boxed_915_, v_stop_boxed_916_, v_b_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v_as_904_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(lean_object* v_f_918_, lean_object* v_v_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
if (lean_obj_tag(v_v_919_) == 0)
{
lean_object* v_code_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_949_; 
v_code_925_ = lean_ctor_get(v_v_919_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_v_919_);
if (v_isSharedCheck_949_ == 0)
{
v___x_927_ = v_v_919_;
v_isShared_928_ = v_isSharedCheck_949_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_code_925_);
lean_dec(v_v_919_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_949_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; 
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
v___x_929_ = lean_apply_6(v_f_918_, v_code_925_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, lean_box(0));
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_940_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_a_930_);
v___x_935_ = v___x_927_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_del_object(v___x_927_);
v_a_941_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_929_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_929_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec_ref(v_f_918_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_v_919_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg___boxed(lean_object* v_f_951_, lean_object* v_v_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_951_, v_v_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(uint8_t v_pu_959_, lean_object* v_f_960_, lean_object* v_v_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v_f_960_, v_v_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___boxed(lean_object* v_pu_968_, lean_object* v_f_969_, lean_object* v_v_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
uint8_t v_pu_boxed_976_; lean_object* v_res_977_; 
v_pu_boxed_976_ = lean_unbox(v_pu_968_);
v_res_977_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0(v_pu_boxed_976_, v_f_969_, v_v_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(lean_object* v___x_978_, uint8_t v_pu_979_, lean_object* v_code_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_st_mk_ref(v___x_978_);
v___x_987_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_Code_elimDead(v_pu_979_, v_code_980_, v___x_986_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_st_ref_get(v___x_986_);
lean_dec(v___x_986_);
lean_dec(v___x_992_);
if (v_isShared_991_ == 0)
{
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_988_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
lean_dec(v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed(lean_object* v___x_997_, lean_object* v_pu_998_, lean_object* v_code_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v_pu_boxed_1005_; lean_object* v_res_1006_; 
v_pu_boxed_1005_ = lean_unbox(v_pu_998_);
v_res_1006_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0(v___x_997_, v_pu_boxed_1005_, v_code_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t v_pu_1007_, lean_object* v_decl_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_toSignature_1014_; lean_object* v_value_1015_; uint8_t v_recursive_1016_; lean_object* v_inlineAttr_x3f_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1044_; 
v_toSignature_1014_ = lean_ctor_get(v_decl_1008_, 0);
v_value_1015_ = lean_ctor_get(v_decl_1008_, 1);
v_recursive_1016_ = lean_ctor_get_uint8(v_decl_1008_, sizeof(void*)*3);
v_inlineAttr_x3f_1017_ = lean_ctor_get(v_decl_1008_, 2);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_decl_1008_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1019_ = v_decl_1008_;
v_isShared_1020_ = v_isSharedCheck_1044_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_inlineAttr_x3f_1017_);
lean_inc(v_value_1015_);
lean_inc(v_toSignature_1014_);
lean_dec(v_decl_1008_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1044_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_box(1);
v___x_1022_ = lean_box(v_pu_1007_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1023_, 0, v___x_1021_);
lean_closure_set(v___f_1023_, 1, v___x_1022_);
v___x_1024_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_elimDeadVars_spec__0___redArg(v___f_1023_, v_value_1015_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1035_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1035_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1035_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1025_);
v___x_1030_ = v___x_1019_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_toSignature_1014_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_a_1025_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_inlineAttr_x3f_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1034_, sizeof(void*)*3, v_recursive_1016_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_1019_);
lean_dec(v_inlineAttr_x3f_1017_);
lean_dec_ref(v_toSignature_1014_);
v_a_1036_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1024_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1024_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed(lean_object* v_pu_1045_, lean_object* v_decl_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
uint8_t v_pu_boxed_1052_; lean_object* v_res_1053_; 
v_pu_boxed_1052_ = lean_unbox(v_pu_1045_);
v_res_1053_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v_pu_boxed_1052_, v_decl_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars(uint8_t v_phase_1057_, lean_object* v_occurrence_1058_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1059_ = ((lean_object*)(l_Lean_Compiler_LCNF_elimDeadVars___closed__1));
v___x_1060_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1057_);
v___x_1061_ = lean_box(v___x_1060_);
v___x_1062_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_elimDeadVars___boxed), 7, 1);
lean_closure_set(v___x_1062_, 0, v___x_1061_);
v___x_1063_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v___x_1059_, v_phase_1057_, v___x_1062_, v_occurrence_1058_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_elimDeadVars___boxed(lean_object* v_phase_1064_, lean_object* v_occurrence_1065_){
_start:
{
uint8_t v_phase_boxed_1066_; lean_object* v_res_1067_; 
v_phase_boxed_1066_ = lean_unbox(v_phase_1064_);
v_res_1067_ = l_Lean_Compiler_LCNF_elimDeadVars(v_phase_boxed_1066_, v_occurrence_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1139_ = 1;
v___x_1140_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_));
v___x_1141_ = l_Lean_registerTraceClass(v___x_1138_, v___x_1139_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2____boxed(lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ElimDead_792928910____hygCtx___hyg_2_();
return v_res_1143_;
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
