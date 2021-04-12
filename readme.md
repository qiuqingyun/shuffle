
# 编译运行

在项目根目录下执行`make`指令，编译生成的可执行文件存放于项目根目录下的`bin`文件夹中。
运行程序前需将`required`文件夹中的文件拷贝至`bin`目录文件夹中。其中包括`cipher_in.txt`文件，保存将要输入程序的密文；`ElGammal.txt`文件保存ElGammal私钥和公钥；`parameters.txt`文件为`p`，`q`，`h`，`g`四个参数。在修改完参数后即可运行编译生成的可执行文件。
Verifier另需Prover生成的三个文件，即`cipher_out.txt`，`Pedersen.txt`和`prove.pro`，一共六个文件才能正常进行验证。
Prover执行`./shuffle 0`，Verifier执行`./shuffle 1`.

# 输出

## Prover

Prover输出一个`cipher_out.txt`文件，包含shuffle后重加密的密文；一个`prove.pro`证明文件；以及一个`Pedersen.txt`文件，包含Pedersen承诺的公钥。另外通过屏幕输出shuffle花费的时间以及生成证明花费的时间。

## Verifier
Verifier输出`ans.txt`结果文件，并通过屏幕输出验证结果以及验证花费的时间。

# 密文

## 输入

将要输入的密文按照特定格式放在`cipher_in.txt`文件中，程序会读取该文件里的密文。若该文件不存在，则程序会自动生成一组随机的密文输入。

## 输入格式

>(u,v)
(u,v)
...  
(u,v)

一共`m`个密文，`m`应为`16`的整数倍，且至少为`32`。  

## 输出

经过shuffle和重加密后的密文输出在`cipher_out.txt`文件中。

# 密钥

ElGammal加密的私钥和公钥放在`ElGammal.txt`文件中，第一行为私钥，第二行为公钥，若该文件不存在则程序会自动随机生成一个。若不需要用到解密功能，则将私钥设置为`0`。

# 参数  

加密参数保存在`parameters.txt`文件中，一共有四行内容,其中前三行为ElGammal参数，第一行为模数`p`，第二行为阶数`q`，第三行为生成元`h`。第四行是Pedersen的生成元`g`。修改文件内容就可以修改参数。  


# 重加密

随机生成`m`个随机数，用这些随机数生成`m`个明文为`1`的密文，再利用同态乘法将shuffle后的密文与密文`1`相乘，即生成了重加密后的密文，保存在`cipher_out.txt`文件中。

