open util/boolean
sig PhoneNumber,Float ,Interger,Time{}

sig Car{
code: Int, 
seats: Int,
}{
code > 0 
seats = 4
}

abstract sig User{ 
phoneNumber: PhoneNumber, 
validCredential: Bool,
validPayment: Bool,
validUser: Bool,
}{validUser=False implies(validCredential=False or validPayment=False)
}

sig RegisteredUser extends User{}

sig Position{
latitude: Float,
longitude: Float
}

sig StartPosition in Position{}

sig FinalPosition in Position{}

sig SafeArea in Position{}

sig Price {
basicPrice:BasicPrice,
battery10DiscountApplied : Bool,
battery20DiscountApplied : Bool,
area30DicountApplied:Bool,
battery30PenaltyApplied : Bool,
}{battery10DiscountApplied =False implies
battery20DiscountApplied= False
}

sig BasicPrice {}

sig Path {
from:StartPosition,
to: FinalPosition
}

abstract sig Order{
path: Path, 
payment: Price,
car: one Car,
PassengerMoreThan2:Bool,
BatteryLevelAtEndMoreThan50:Bool,
BatteryLevelAtEndLessThan20:Bool,
Finaldistancefromsafestationgreaterthan3km: Bool,
CarLeftAtSpecialParking:Bool,
}{BatteryLevelAtEndMoreThan50!=
BatteryLevelAtEndLessThan20
}

sig SharedOrder extends Order{}
sig SingleOrder extends Order{}

sig Reservation{
resCode :one Int,
resCapacity:Int,
resUser:one User,
resCar: one Car,
resTime: one Time
}



fact CarsCodeAreUnique {/*car code is unique*/
all c1, c2: Car | (c1 != c2) => c1.code != c2.code
}

fact UsersAreUnique {/*user phone number is unique*/
all u1, u2: User | (u1 != u2) => u1.phoneNumber != u2.phoneNumber
}

fact ReservationsAreUnique {/*reservation code is unique*/
all r1, r2: Reservation | (r1 != r2) => r1.resCode != r2.resCode
}

fact {/*path cannot go to  a position to itself*/
all x: Path |x.from !=x. to    
}

assert resUserisValidUser{all u:User|/*reservation user should be valid user*/
u.validUser=False implies not (u.validCredential=True and u.validPayment =True)
}

check resUserisValidUser for 3 expect 0

pred NoCarBothInUseandinReservation[c: Car]{/*car cannot be in  use and also in reservation*/
all r:Reservation, o:Order |not (c in r.resCar) and not(c in o.car)
}

fact batterya10DiscountApplied{/*battery discount criteria*/
all o:Order,p: Price|(o.PassengerMoreThan2=True) implies (p in o.payment and p.battery10DiscountApplied=True)  else
(o.PassengerMoreThan2=False) implies (p in o.payment and p.battery10DiscountApplied=False) 
}

fact batterya20DiscountApplied{/*battery discount criteria*/
all o:Order,p: Price|(o.BatteryLevelAtEndMoreThan50=True) implies (p in o.payment and p.battery20DiscountApplied=True)  else
(o.BatteryLevelAtEndMoreThan50=False) implies (p in o.payment and p.battery20DiscountApplied=False) 
}

fact battery30PenaltyApplied{/*battery and area penalty criteria*/
all o:Order,p: Price|(o.Finaldistancefromsafestationgreaterthan3km=True or o.BatteryLevelAtEndLessThan20=True) implies 
(p in o.payment and p.battery30PenaltyApplied=True)
}

fact area30DicountApplied{/*battery penalty criteria*/
all o:Order,p: Price|(o.CarLeftAtSpecialParking=True) implies (p in o.payment and p.area30DicountApplied=True)
}

assert NoBatteryLogicError{all p:Price|
p.battery10DiscountApplied =False and p.battery20DiscountApplied= False
}
check  NoBatteryLogicError for 3 expect 0



pred show() {}

run show 
run NoCarBothInUseandinReservation











 

