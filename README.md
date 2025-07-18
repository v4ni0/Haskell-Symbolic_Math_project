
# Проект към курс “Функционално програмиране” за специалности Информатика, Компютърни науки (2 поток) и избираема дисциплина зимен семестър 2024/25 г.

Система за символно смятане

## Synopsis: Да се реализира проста система за символни манипулации на алгебрични изрази.
## Системите за символно смятане работят с алгебрични изрази, представени като дървета. По същество те автоматизират алгоритмични стъпки от обработката на изрази, сред които: 
1. съкращаване
2. разкриване на скоби
3. изваждане на общ множител пред скоби
4. привеждане под общ знаменател
5. диференциране
6. интегриране

Целта на проекта е да се реализира система, която позволява въвеждане на алгебрични изрази и изпълняване на алгебрични операции над тях. Като минимум трябва да се поддържат операциите изброени по-горе. Изразите да бъдат построени от числа (константи) и променливи с аритметичните операции (+, -, *, /) и степенуване. Изразите да могат да бъдат въвеждани и извеждани като низове. Примерен синтаксис за изрази:

<променлива> ::= <главна-латинска-буква>{<латинска-буква-или-цифра>}
<число> ::= [+|-]<цифра>{<цифра>}[.{<цифра>}]
<атом> ::= <число> | <променлива> | (<израз>) | <функция>(<израз>)
<множител> ::= <атом> | <атом>^<множител>
<терм> ::= <множител> | <множител> * <терм> | <множител> / <терм>
<израз> ::= <терм> | <израз> + <терм> | <израз> - <терм>


