package controller;

import model.beans.Utente;
import model.beans.WishList;
import services.WishlistService;

import utils.ResponseUtils;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "WishlistServlet", value = "/WishlistServlet")
public class WishlistServlet extends HttpServlet {
    private WishlistService wishlistService;

    @Override
    public void init() throws ServletException {
        try {
            this.wishlistService = new WishlistService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize WishlistService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            try {
                int cod = Integer.parseInt(request.getParameter("cod"));

                // aggiungo alla wishlist
                if (cod == 1) {
                    if (request.getSession().getAttribute("user") == null) {
                        response.sendRedirect(request.getServletContext().getContextPath() + "/login.jsp");
                        return;
                    }

                    int p = Integer.parseInt(request.getParameter("prodotto"));
                    Utente u = (Utente) request.getSession().getAttribute("user");
                    wishlistService.addToWishList(u, p);
                    response.sendRedirect(request.getServletContext().getContextPath() + "/landingpage");
                }
                // ottengo la wishlist
                else if (cod == 2) {
                    Utente u = (Utente) request.getSession().getAttribute("user");
                    WishList w = wishlistService.getWishListByUser(u);
                    request.setAttribute("wishlist", w);

                    String address = "/wishlist.jsp";
                    RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                    dispatcher.forward(request, response);
                }
                // elimino dalla wishlist
                else if (cod == 3) {
                    int id_utente = Integer.parseInt(request.getParameter("id_utente"));
                    int id_prodotto = Integer.parseInt(request.getParameter("id_prodotto"));
                    wishlistService.removeFromWishList(id_utente, id_prodotto);
                }

            } catch (SQLException throwables) {
                throwables.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        } catch (Exception e) {
            e.printStackTrace();
            ResponseUtils.sendError(response, HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            doGet(request, response);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
