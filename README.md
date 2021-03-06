![4ctImg01](https://user-images.githubusercontent.com/34955220/71302741-526aa500-23f2-11ea-90c4-6ad7a5faf1ea.jpg)  

# 4CT_FSharp
四色定理をF#に移植したよ  
Ruby→https://github.com/righ1113/4CT_Ruby  

# 変更履歴
21/03/21　役目は果たした  
20/07/12　Reduce, Discharge 二周目終了、Reduce と Discharge の deg=7 は動く  
20/03/09　Reduce 二周目終了  
20/02/16　Reduce, Discharge 一周目終了  
19/12/27　ver1srcに移行  
19/12/21　init.  

# 四色定理とは
四色定理（よんしょくていり／ししょくていり、英: Four color theorem）とは、  
厳密ではないが日常的な直感で説明すると  
「平面上のいかなる地図も、隣接する領域が異なる色になるように塗り分けるには4色あれば十分だ」という定理である。 

グラフ理論でとらえると、  
- 「平面グラフは4彩色可能である」  

という定理になる。  

（Wikipediaより）  

# 参考文献

リンクは新しいタブで開いてください。  

### 「RSST」  
[The Four Color Theorem](http://people.math.gatech.edu/~thomas/FC/fourcolor.html)  
Neil Robertson, Daniel P. Sanders, Paul Seymour and Robin Thomasらによる、  
オリジナルの証明を改良したもの。C言語で書かれている。  
本Repositoryでは、これをF#に移植することを目標にする。  

### 「四色定理の証明」　山森千絵,　指導教員：杉浦洋  
[link](http://www.st.nanzan-u.ac.jp/info/gr-thesis/ms/2009/06mi203.pdf)  
RSSTに沿った内容のpdf。日本語。  

### 「Coq-proof」  
[Formal proof of the Four Color Theorem](https://github.com/math-comp/fourcolor)  
Georges Gonthierによる、定理証明支援系Coqを用いた証明。  

### 「四色問題」　Robin Wilson 著,　茂木健一郎 訳   
[link](https://www.amazon.co.jp/%E5%9B%9B%E8%89%B2%E5%95%8F%E9%A1%8C-%E6%96%B0%E6%BD%AE%E6%96%87%E5%BA%AB-%E3%83%AD%E3%83%93%E3%83%B3-%E3%82%A6%E3%82%A3%E3%83%AB%E3%82%BD%E3%83%B3/dp/4102184619)  
一般向けの解説書。これは良書。  

### 「四色問題 どう解かれ何をもたらしたのか」　一松信 著  
[link](https://www.amazon.co.jp/%E5%9B%9B%E8%89%B2%E5%95%8F%E9%A1%8C-%E3%81%A9%E3%81%86%E8%A7%A3%E3%81%8B%E3%82%8C%E4%BD%95%E3%82%92%E3%82%82%E3%81%9F%E3%82%89%E3%81%97%E3%81%9F%E3%81%AE%E3%81%8B-%E3%83%96%E3%83%AB%E3%83%BC%E3%83%90%E3%83%83%E3%82%AF%E3%82%B9-%E4%B8%80%E6%9D%BE-%E4%BF%A1/dp/4062579693)  
こちらはやや専門的。  

# 証明&プログラムの説明
[Wiki](https://github.com/righ1113/4CT_FSharp/wiki)をみてね  
  
  
  
