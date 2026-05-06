/-!
# 项目级配置

本文件中的运行时常数只是工程防护，不属于渐近安全定义的一部分。
-/

namespace LeanCryptoProtocols

/--
默认控制器激活次数预算。

UC 安全参数单独作为分布族索引记录；
这个常数只用于可执行测试入口中防止意外不终止。
-/
def max_controller_steps : Nat := 1000000

end LeanCryptoProtocols
