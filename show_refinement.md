--show-refinementの問題点
Z3のsimpifyを使うことで、関数適用などを消した。
しかし、仮にexistsが結果に残ると表示できない
  * 残ることも有りうる？
  * 残る場合、rtypeの構文を変えるのはまずい？
refinement typeの括弧の出力が冗長で見にくい
refinement typeの表示のときにsimplifyが重いときがあるが、ソルバ本体は別途時間を計測している